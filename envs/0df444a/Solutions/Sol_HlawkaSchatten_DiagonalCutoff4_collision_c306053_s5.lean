-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306053_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:55:57.596901+00:00
-- url     : https://prove2.me/submissions/5dd7229f-b413-4e02-958d-3b661719601e

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
theorem collision_support_c306053_s5_s5_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2585403563/10000000000 : ℝ)*x 0 + (1273161543/2500000000 : ℝ)*x 1 + (511068457/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585403563/10000000000 : ℝ)^17 ≤ (3410341176889/20000000000000 : ℝ)^13 := by
    have hnat : (2585403563 : ℕ)^17*20000000000000^13 ≤ 3410341176889^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585403563 10000000000 3410341176889 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1273161543/2500000000 : ℝ)^17 ≤ (2068913234711/5000000000000 : ℝ)^13 := by
    have hnat : (1273161543 : ℕ)^17*5000000000000^13 ≤ 2068913234711^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273161543 2500000000 2068913234711 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511068457/1000000000 : ℝ)^17 ≤ (8314005882527/20000000000000 : ℝ)^13 := by
    have hnat : (511068457 : ℕ)^17*20000000000000^13 ≤ 8314005882527^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511068457 1000000000 8314005882527 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2585403563/10000000000 : ℝ), (1273161543/2500000000 : ℝ), (511068457/1000000000 : ℝ)] ![(3410341176889/20000000000000 : ℝ), (2068913234711/5000000000000 : ℝ), (8314005882527/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2585403563/10000000000 : ℝ)|^17 ≤ (3410341176889/20000000000000 : ℝ)^13
        have hw : |(-2585403563/10000000000 : ℝ)|=(2585403563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1273161543/2500000000 : ℝ)|^17 ≤ (2068913234711/5000000000000 : ℝ)^13
        have hw : |(1273161543/2500000000 : ℝ)|=(1273161543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(511068457/1000000000 : ℝ)|^17 ≤ (8314005882527/20000000000000 : ℝ)^13
        have hw : |(511068457/1000000000 : ℝ)|=(511068457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4524291997/10000000000 : ℝ)*x 0 + (-1053981647/5000000000 : ℝ)*x 1 + (3010044073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4524291997/10000000000 : ℝ)^17 ≤ (35445915988757/100000000000000 : ℝ)^13 := by
    have hnat : (4524291997 : ℕ)^17*100000000000000^13 ≤ 35445915988757^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524291997 10000000000 35445915988757 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053981647/5000000000 : ℝ)^17 ≤ (13056323554691/100000000000000 : ℝ)^13 := by
    have hnat : (1053981647 : ℕ)^17*100000000000000^13 ≤ 13056323554691^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053981647 5000000000 13056323554691 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3010044073/5000000000 : ℝ)^17 ≤ (10299552087417/20000000000000 : ℝ)^13 := by
    have hnat : (3010044073 : ℕ)^17*20000000000000^13 ≤ 10299552087417^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3010044073 5000000000 10299552087417 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4524291997/10000000000 : ℝ), (-1053981647/5000000000 : ℝ), (3010044073/5000000000 : ℝ)] ![(35445915988757/100000000000000 : ℝ), (13056323554691/100000000000000 : ℝ), (10299552087417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4524291997/10000000000 : ℝ)|^17 ≤ (35445915988757/100000000000000 : ℝ)^13
        have hw : |(4524291997/10000000000 : ℝ)|=(4524291997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1053981647/5000000000 : ℝ)|^17 ≤ (13056323554691/100000000000000 : ℝ)^13
        have hw : |(-1053981647/5000000000 : ℝ)|=(1053981647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3010044073/5000000000 : ℝ)|^17 ≤ (10299552087417/20000000000000 : ℝ)^13
        have hw : |(3010044073/5000000000 : ℝ)|=(3010044073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (908631487/2000000000 : ℝ)*x 0 + (1202457909/2000000000 : ℝ)*x 1 + (-1047420501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (908631487/2000000000 : ℝ)^17 ≤ (7127864072061/20000000000000 : ℝ)^13 := by
    have hnat : (908631487 : ℕ)^17*20000000000000^13 ≤ 7127864072061^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908631487 2000000000 7127864072061 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1202457909/2000000000 : ℝ)^17 ≤ (25705269707207/50000000000000 : ℝ)^13 := by
    have hnat : (1202457909 : ℕ)^17*50000000000000^13 ≤ 25705269707207^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202457909 2000000000 25705269707207 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047420501/5000000000 : ℝ)^17 ≤ (6475070105147/50000000000000 : ℝ)^13 := by
    have hnat : (1047420501 : ℕ)^17*50000000000000^13 ≤ 6475070105147^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047420501 5000000000 6475070105147 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(908631487/2000000000 : ℝ), (1202457909/2000000000 : ℝ), (-1047420501/5000000000 : ℝ)] ![(7127864072061/20000000000000 : ℝ), (25705269707207/50000000000000 : ℝ), (6475070105147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(908631487/2000000000 : ℝ)|^17 ≤ (7127864072061/20000000000000 : ℝ)^13
        have hw : |(908631487/2000000000 : ℝ)|=(908631487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1202457909/2000000000 : ℝ)|^17 ≤ (25705269707207/50000000000000 : ℝ)^13
        have hw : |(1202457909/2000000000 : ℝ)|=(1202457909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047420501/5000000000 : ℝ)|^17 ≤ (6475070105147/50000000000000 : ℝ)^13
        have hw : |(-1047420501/5000000000 : ℝ)|=(1047420501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6421641417/10000000000 : ℝ)*x 0 + (126118509/400000000 : ℝ)*x 1 + (1563162943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6421641417/10000000000 : ℝ)^17 ≤ (56035108932569/100000000000000 : ℝ)^13 := by
    have hnat : (6421641417 : ℕ)^17*100000000000000^13 ≤ 56035108932569^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6421641417 10000000000 56035108932569 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126118509/400000000 : ℝ)^17 ≤ (2763048393517/12500000000000 : ℝ)^13 := by
    have hnat : (126118509 : ℕ)^17*12500000000000^13 ≤ 2763048393517^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126118509 400000000 2763048393517 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1563162943/5000000000 : ℝ)^17 ≤ (21860503904959/100000000000000 : ℝ)^13 := by
    have hnat : (1563162943 : ℕ)^17*100000000000000^13 ≤ 21860503904959^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1563162943 5000000000 21860503904959 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6421641417/10000000000 : ℝ), (126118509/400000000 : ℝ), (1563162943/5000000000 : ℝ)] ![(56035108932569/100000000000000 : ℝ), (2763048393517/12500000000000 : ℝ), (21860503904959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6421641417/10000000000 : ℝ)|^17 ≤ (56035108932569/100000000000000 : ℝ)^13
        have hw : |(6421641417/10000000000 : ℝ)|=(6421641417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126118509/400000000 : ℝ)|^17 ≤ (2763048393517/12500000000000 : ℝ)^13
        have hw : |(126118509/400000000 : ℝ)|=(126118509/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1563162943/5000000000 : ℝ)|^17 ≤ (21860503904959/100000000000000 : ℝ)^13
        have hw : |(1563162943/5000000000 : ℝ)|=(1563162943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1250252403/5000000000 : ℝ)*x 0 + (2116948219/5000000000 : ℝ)*x 1 + (5991322939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1250252403/5000000000 : ℝ)^17 ≤ (8161602699219/50000000000000 : ℝ)^13 := by
    have hnat : (1250252403 : ℕ)^17*50000000000000^13 ≤ 8161602699219^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250252403 5000000000 8161602699219 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116948219/5000000000 : ℝ)^17 ≤ (6500115397623/20000000000000 : ℝ)^13 := by
    have hnat : (2116948219 : ℕ)^17*20000000000000^13 ≤ 6500115397623^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116948219 5000000000 6500115397623 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5991322939/10000000000 : ℝ)^17 ≤ (409409740789/800000000000 : ℝ)^13 := by
    have hnat : (5991322939 : ℕ)^17*800000000000^13 ≤ 409409740789^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5991322939 10000000000 409409740789 800000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1250252403/5000000000 : ℝ), (2116948219/5000000000 : ℝ), (5991322939/10000000000 : ℝ)] ![(8161602699219/50000000000000 : ℝ), (6500115397623/20000000000000 : ℝ), (409409740789/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1250252403/5000000000 : ℝ)|^17 ≤ (8161602699219/50000000000000 : ℝ)^13
        have hw : |(-1250252403/5000000000 : ℝ)|=(1250252403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2116948219/5000000000 : ℝ)|^17 ≤ (6500115397623/20000000000000 : ℝ)^13
        have hw : |(2116948219/5000000000 : ℝ)|=(2116948219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5991322939/10000000000 : ℝ)|^17 ≤ (409409740789/800000000000 : ℝ)^13
        have hw : |(5991322939/10000000000 : ℝ)|=(5991322939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4264865849/10000000000 : ℝ)*x 0 + (-854488379/5000000000 : ℝ)*x 1 + (6529140991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4264865849/10000000000 : ℝ)^17 ≤ (8202950946199/25000000000000 : ℝ)^13 := by
    have hnat : (4264865849 : ℕ)^17*25000000000000^13 ≤ 8202950946199^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4264865849 10000000000 8202950946199 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854488379/5000000000 : ℝ)^17 ≤ (9923273783549/100000000000000 : ℝ)^13 := by
    have hnat : (854488379 : ℕ)^17*100000000000000^13 ≤ 9923273783549^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854488379 5000000000 9923273783549 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6529140991/10000000000 : ℝ)^17 ≤ (11452984484931/20000000000000 : ℝ)^13 := by
    have hnat : (6529140991 : ℕ)^17*20000000000000^13 ≤ 11452984484931^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6529140991 10000000000 11452984484931 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4264865849/10000000000 : ℝ), (-854488379/5000000000 : ℝ), (6529140991/10000000000 : ℝ)] ![(8202950946199/25000000000000 : ℝ), (9923273783549/100000000000000 : ℝ), (11452984484931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4264865849/10000000000 : ℝ)|^17 ≤ (8202950946199/25000000000000 : ℝ)^13
        have hw : |(4264865849/10000000000 : ℝ)|=(4264865849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-854488379/5000000000 : ℝ)|^17 ≤ (9923273783549/100000000000000 : ℝ)^13
        have hw : |(-854488379/5000000000 : ℝ)|=(854488379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6529140991/10000000000 : ℝ)|^17 ≤ (11452984484931/20000000000000 : ℝ)^13
        have hw : |(6529140991/10000000000 : ℝ)|=(6529140991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4283833203/10000000000 : ℝ)*x 0 + (3399391913/5000000000 : ℝ)*x 1 + (-1254049379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283833203/10000000000 : ℝ)^17 ≤ (4125344999629/12500000000000 : ℝ)^13 := by
    have hnat : (4283833203 : ℕ)^17*12500000000000^13 ≤ 4125344999629^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283833203 10000000000 4125344999629 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3399391913/5000000000 : ℝ)^17 ≤ (6037701136381/10000000000000 : ℝ)^13 := by
    have hnat : (3399391913 : ℕ)^17*10000000000000^13 ≤ 6037701136381^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3399391913 5000000000 6037701136381 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1254049379/10000000000 : ℝ)^17 ≤ (1655057155049/25000000000000 : ℝ)^13 := by
    have hnat : (1254049379 : ℕ)^17*25000000000000^13 ≤ 1655057155049^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254049379 10000000000 1655057155049 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283833203/10000000000 : ℝ), (3399391913/5000000000 : ℝ), (-1254049379/10000000000 : ℝ)] ![(4125344999629/12500000000000 : ℝ), (6037701136381/10000000000000 : ℝ), (1655057155049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283833203/10000000000 : ℝ)|^17 ≤ (4125344999629/12500000000000 : ℝ)^13
        have hw : |(4283833203/10000000000 : ℝ)|=(4283833203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3399391913/5000000000 : ℝ)|^17 ≤ (6037701136381/10000000000000 : ℝ)^13
        have hw : |(3399391913/5000000000 : ℝ)|=(3399391913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1254049379/10000000000 : ℝ)|^17 ≤ (1655057155049/25000000000000 : ℝ)^13
        have hw : |(-1254049379/10000000000 : ℝ)|=(1254049379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3107468453/5000000000 : ℝ)*x 0 + (4287165737/10000000000 : ℝ)*x 1 + (1067483263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3107468453/5000000000 : ℝ)^17 ≤ (2684409686813/5000000000000 : ℝ)^13 := by
    have hnat : (3107468453 : ℕ)^17*5000000000000^13 ≤ 2684409686813^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107468453 5000000000 2684409686813 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4287165737/10000000000 : ℝ)^17 ≤ (412954220137/1250000000000 : ℝ)^13 := by
    have hnat : (4287165737 : ℕ)^17*1250000000000^13 ≤ 412954220137^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287165737 10000000000 412954220137 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1067483263/5000000000 : ℝ)^17 ≤ (3318867158553/25000000000000 : ℝ)^13 := by
    have hnat : (1067483263 : ℕ)^17*25000000000000^13 ≤ 3318867158553^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067483263 5000000000 3318867158553 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3107468453/5000000000 : ℝ), (4287165737/10000000000 : ℝ), (1067483263/5000000000 : ℝ)] ![(2684409686813/5000000000000 : ℝ), (412954220137/1250000000000 : ℝ), (3318867158553/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3107468453/5000000000 : ℝ)|^17 ≤ (2684409686813/5000000000000 : ℝ)^13
        have hw : |(3107468453/5000000000 : ℝ)|=(3107468453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4287165737/10000000000 : ℝ)|^17 ≤ (412954220137/1250000000000 : ℝ)^13
        have hw : |(4287165737/10000000000 : ℝ)|=(4287165737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1067483263/5000000000 : ℝ)|^17 ≤ (3318867158553/25000000000000 : ℝ)^13
        have hw : |(1067483263/5000000000 : ℝ)|=(1067483263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-431374289/2500000000 : ℝ)*x 0 + (2463954087/5000000000 : ℝ)*x 1 + (369625979/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431374289/2500000000 : ℝ)^17 ≤ (5024451241639/50000000000000 : ℝ)^13 := by
    have hnat : (431374289 : ℕ)^17*50000000000000^13 ≤ 5024451241639^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431374289 2500000000 5024451241639 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2463954087/5000000000 : ℝ)^17 ≤ (39636678572553/100000000000000 : ℝ)^13 := by
    have hnat : (2463954087 : ℕ)^17*100000000000000^13 ≤ 39636678572553^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463954087 5000000000 39636678572553 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (369625979/625000000 : ℝ)^17 ≤ (50314418918939/100000000000000 : ℝ)^13 := by
    have hnat : (369625979 : ℕ)^17*100000000000000^13 ≤ 50314418918939^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369625979 625000000 50314418918939 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431374289/2500000000 : ℝ), (2463954087/5000000000 : ℝ), (369625979/625000000 : ℝ)] ![(5024451241639/50000000000000 : ℝ), (39636678572553/100000000000000 : ℝ), (50314418918939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431374289/2500000000 : ℝ)|^17 ≤ (5024451241639/50000000000000 : ℝ)^13
        have hw : |(-431374289/2500000000 : ℝ)|=(431374289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2463954087/5000000000 : ℝ)|^17 ≤ (39636678572553/100000000000000 : ℝ)^13
        have hw : |(2463954087/5000000000 : ℝ)|=(2463954087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(369625979/625000000 : ℝ)|^17 ≤ (50314418918939/100000000000000 : ℝ)^13
        have hw : |(369625979/625000000 : ℝ)|=(369625979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (512867603/1250000000 : ℝ)*x 0 + (-1860881389/10000000000 : ℝ)*x 1 + (6568390749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512867603/1250000000 : ℝ)^17 ≤ (3119231721863/10000000000000 : ℝ)^13 := by
    have hnat : (512867603 : ℕ)^17*10000000000000^13 ≤ 3119231721863^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512867603 1250000000 3119231721863 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1860881389/10000000000 : ℝ)^17 ≤ (11092175993327/100000000000000 : ℝ)^13 := by
    have hnat : (1860881389 : ℕ)^17*100000000000000^13 ≤ 11092175993327^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860881389 10000000000 11092175993327 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6568390749/10000000000 : ℝ)^17 ≤ (57715506766097/100000000000000 : ℝ)^13 := by
    have hnat : (6568390749 : ℕ)^17*100000000000000^13 ≤ 57715506766097^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6568390749 10000000000 57715506766097 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(512867603/1250000000 : ℝ), (-1860881389/10000000000 : ℝ), (6568390749/10000000000 : ℝ)] ![(3119231721863/10000000000000 : ℝ), (11092175993327/100000000000000 : ℝ), (57715506766097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(512867603/1250000000 : ℝ)|^17 ≤ (3119231721863/10000000000000 : ℝ)^13
        have hw : |(512867603/1250000000 : ℝ)|=(512867603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1860881389/10000000000 : ℝ)|^17 ≤ (11092175993327/100000000000000 : ℝ)^13
        have hw : |(-1860881389/10000000000 : ℝ)|=(1860881389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6568390749/10000000000 : ℝ)|^17 ≤ (57715506766097/100000000000000 : ℝ)^13
        have hw : |(6568390749/10000000000 : ℝ)|=(6568390749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (544248479/1000000000 : ℝ)*x 0 + (5678195673/10000000000 : ℝ)*x 1 + (-665678209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544248479/1000000000 : ℝ)^17 ≤ (45134024691321/100000000000000 : ℝ)^13 := by
    have hnat : (544248479 : ℕ)^17*100000000000000^13 ≤ 45134024691321^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544248479 1000000000 45134024691321 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5678195673/10000000000 : ℝ)^17 ≤ (47707072924059/100000000000000 : ℝ)^13 := by
    have hnat : (5678195673 : ℕ)^17*100000000000000^13 ≤ 47707072924059^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5678195673 10000000000 47707072924059 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (665678209/5000000000 : ℝ)^17 ≤ (7158902368537/100000000000000 : ℝ)^13 := by
    have hnat : (665678209 : ℕ)^17*100000000000000^13 ≤ 7158902368537^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665678209 5000000000 7158902368537 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544248479/1000000000 : ℝ), (5678195673/10000000000 : ℝ), (-665678209/5000000000 : ℝ)] ![(45134024691321/100000000000000 : ℝ), (47707072924059/100000000000000 : ℝ), (7158902368537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544248479/1000000000 : ℝ)|^17 ≤ (45134024691321/100000000000000 : ℝ)^13
        have hw : |(544248479/1000000000 : ℝ)|=(544248479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5678195673/10000000000 : ℝ)|^17 ≤ (47707072924059/100000000000000 : ℝ)^13
        have hw : |(5678195673/10000000000 : ℝ)|=(5678195673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-665678209/5000000000 : ℝ)|^17 ≤ (7158902368537/100000000000000 : ℝ)^13
        have hw : |(-665678209/5000000000 : ℝ)|=(665678209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (918969127/1250000000 : ℝ)*x 0 + (2977308499/10000000000 : ℝ)*x 1 + (12832411/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (918969127/1250000000 : ℝ)^17 ≤ (66877559845703/100000000000000 : ℝ)^13 := by
    have hnat : (918969127 : ℕ)^17*100000000000000^13 ≤ 66877559845703^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918969127 1250000000 66877559845703 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2977308499/10000000000 : ℝ)^17 ≤ (5127002013879/25000000000000 : ℝ)^13 := by
    have hnat : (2977308499 : ℕ)^17*25000000000000^13 ≤ 5127002013879^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2977308499 10000000000 5127002013879 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12832411/62500000 : ℝ)^17 ≤ (6307216044943/50000000000000 : ℝ)^13 := by
    have hnat : (12832411 : ℕ)^17*50000000000000^13 ≤ 6307216044943^13*62500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12832411 62500000 6307216044943 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(918969127/1250000000 : ℝ), (2977308499/10000000000 : ℝ), (12832411/62500000 : ℝ)] ![(66877559845703/100000000000000 : ℝ), (5127002013879/25000000000000 : ℝ), (6307216044943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(918969127/1250000000 : ℝ)|^17 ≤ (66877559845703/100000000000000 : ℝ)^13
        have hw : |(918969127/1250000000 : ℝ)|=(918969127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2977308499/10000000000 : ℝ)|^17 ≤ (5127002013879/25000000000000 : ℝ)^13
        have hw : |(2977308499/10000000000 : ℝ)|=(2977308499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12832411/62500000 : ℝ)|^17 ≤ (6307216044943/50000000000000 : ℝ)^13
        have hw : |(12832411/62500000 : ℝ)|=(12832411/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1638988009/10000000000 : ℝ)*x 0 + (1097340887/2000000000 : ℝ)*x 1 + (678656997/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1638988009/10000000000 : ℝ)^17 ≤ (1879043265543/20000000000000 : ℝ)^13 := by
    have hnat : (1638988009 : ℕ)^17*20000000000000^13 ≤ 1879043265543^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1638988009 10000000000 1879043265543 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097340887/2000000000 : ℝ)^17 ≤ (9122833221313/20000000000000 : ℝ)^13 := by
    have hnat : (1097340887 : ℕ)^17*20000000000000^13 ≤ 9122833221313^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097340887 2000000000 9122833221313 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678656997/1250000000 : ℝ)^17 ≤ (44990617545387/100000000000000 : ℝ)^13 := by
    have hnat : (678656997 : ℕ)^17*100000000000000^13 ≤ 44990617545387^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678656997 1250000000 44990617545387 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1638988009/10000000000 : ℝ), (1097340887/2000000000 : ℝ), (678656997/1250000000 : ℝ)] ![(1879043265543/20000000000000 : ℝ), (9122833221313/20000000000000 : ℝ), (44990617545387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1638988009/10000000000 : ℝ)|^17 ≤ (1879043265543/20000000000000 : ℝ)^13
        have hw : |(-1638988009/10000000000 : ℝ)|=(1638988009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097340887/2000000000 : ℝ)|^17 ≤ (9122833221313/20000000000000 : ℝ)^13
        have hw : |(1097340887/2000000000 : ℝ)|=(1097340887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678656997/1250000000 : ℝ)|^17 ≤ (44990617545387/100000000000000 : ℝ)^13
        have hw : |(678656997/1250000000 : ℝ)|=(678656997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1102004877/2000000000 : ℝ)*x 0 + (-1415022117/10000000000 : ℝ)*x 1 + (2778473927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102004877/2000000000 : ℝ)^17 ≤ (716685266437/1562500000000 : ℝ)^13 := by
    have hnat : (1102004877 : ℕ)^17*1562500000000^13 ≤ 716685266437^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102004877 2000000000 716685266437 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1415022117/10000000000 : ℝ)^17 ≤ (484551143927/6250000000000 : ℝ)^13 := by
    have hnat : (1415022117 : ℕ)^17*6250000000000^13 ≤ 484551143927^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415022117 10000000000 484551143927 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2778473927/5000000000 : ℝ)^17 ≤ (2898707790097/6250000000000 : ℝ)^13 := by
    have hnat : (2778473927 : ℕ)^17*6250000000000^13 ≤ 2898707790097^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2778473927 5000000000 2898707790097 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102004877/2000000000 : ℝ), (-1415022117/10000000000 : ℝ), (2778473927/5000000000 : ℝ)] ![(716685266437/1562500000000 : ℝ), (484551143927/6250000000000 : ℝ), (2898707790097/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102004877/2000000000 : ℝ)|^17 ≤ (716685266437/1562500000000 : ℝ)^13
        have hw : |(1102004877/2000000000 : ℝ)|=(1102004877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1415022117/10000000000 : ℝ)|^17 ≤ (484551143927/6250000000000 : ℝ)^13
        have hw : |(-1415022117/10000000000 : ℝ)|=(1415022117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2778473927/5000000000 : ℝ)|^17 ≤ (2898707790097/6250000000000 : ℝ)^13
        have hw : |(2778473927/5000000000 : ℝ)|=(2778473927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (816494753/2000000000 : ℝ)*x 0 + (6707449329/10000000000 : ℝ)*x 1 + (-419623939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (816494753/2000000000 : ℝ)^17 ≤ (15494498729723/50000000000000 : ℝ)^13 := by
    have hnat : (816494753 : ℕ)^17*50000000000000^13 ≤ 15494498729723^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      816494753 2000000000 15494498729723 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6707449329/10000000000 : ℝ)^17 ≤ (29659269560549/50000000000000 : ℝ)^13 := by
    have hnat : (6707449329 : ℕ)^17*50000000000000^13 ≤ 29659269560549^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6707449329 10000000000 29659269560549 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419623939/2500000000 : ℝ)^17 ≤ (969246340149/10000000000000 : ℝ)^13 := by
    have hnat : (419623939 : ℕ)^17*10000000000000^13 ≤ 969246340149^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419623939 2500000000 969246340149 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(816494753/2000000000 : ℝ), (6707449329/10000000000 : ℝ), (-419623939/2500000000 : ℝ)] ![(15494498729723/50000000000000 : ℝ), (29659269560549/50000000000000 : ℝ), (969246340149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(816494753/2000000000 : ℝ)|^17 ≤ (15494498729723/50000000000000 : ℝ)^13
        have hw : |(816494753/2000000000 : ℝ)|=(816494753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6707449329/10000000000 : ℝ)|^17 ≤ (29659269560549/50000000000000 : ℝ)^13
        have hw : |(6707449329/10000000000 : ℝ)|=(6707449329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419623939/2500000000 : ℝ)|^17 ≤ (969246340149/10000000000000 : ℝ)^13
        have hw : |(-419623939/2500000000 : ℝ)|=(419623939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306053_s5_s5_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7433928339/10000000000 : ℝ)*x 0 + (495897549/2000000000 : ℝ)*x 1 + (2462459827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7433928339/10000000000 : ℝ)^17 ≤ (2714271238749/4000000000000 : ℝ)^13 := by
    have hnat : (7433928339 : ℕ)^17*4000000000000^13 ≤ 2714271238749^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7433928339 10000000000 2714271238749 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495897549/2000000000 : ℝ)^17 ≤ (8072012135891/50000000000000 : ℝ)^13 := by
    have hnat : (495897549 : ℕ)^17*50000000000000^13 ≤ 8072012135891^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495897549 2000000000 8072012135891 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2462459827/10000000000 : ℝ)^17 ≤ (7999597369031/50000000000000 : ℝ)^13 := by
    have hnat : (2462459827 : ℕ)^17*50000000000000^13 ≤ 7999597369031^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462459827 10000000000 7999597369031 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7433928339/10000000000 : ℝ), (495897549/2000000000 : ℝ), (2462459827/10000000000 : ℝ)] ![(2714271238749/4000000000000 : ℝ), (8072012135891/50000000000000 : ℝ), (7999597369031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7433928339/10000000000 : ℝ)|^17 ≤ (2714271238749/4000000000000 : ℝ)^13
        have hw : |(7433928339/10000000000 : ℝ)|=(7433928339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(495897549/2000000000 : ℝ)|^17 ≤ (8072012135891/50000000000000 : ℝ)^13
        have hw : |(495897549/2000000000 : ℝ)|=(495897549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2462459827/10000000000 : ℝ)|^17 ≤ (7999597369031/50000000000000 : ℝ)^13
        have hw : |(2462459827/10000000000 : ℝ)|=(2462459827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306053_s5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((11807/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11807/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13671/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13671/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53301/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(53301/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29567/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29567/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34201/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34201/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3293/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3293/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (11807/25000 : ℝ) ^ (67/16 : ℝ) ≤ (4322257481974991957/100000000000000000000 : ℝ) := by
    have hpowers : (11807/25000 : ℝ)^67 ≤ (4322257481974991957/100000000000000000000 : ℝ)^16 := by
      have hnat : (11807 : ℕ)^67*100000000000000000000^16 ≤ 4322257481974991957^16*25000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11807 25000 4322257481974991957 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11807/25000 : ℝ)) (X := (4322257481974991957/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner0a : (104322257481974991957/100000000000000000000 : ℝ) ≤ (404062478086337/400000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (104322257481974991957/100000000000000000000 : ℝ)^16 ≤ (404062478086337/400000000000000 : ℝ)^67 := by
      have hnat : (104322257481974991957 : ℕ)^16*400000000000000^67 ≤ 404062478086337^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104322257481974991957 100000000000000000000 404062478086337 400000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (404062478086337/400000000000000 : ℝ)) (X := (104322257481974991957/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner0b : (54322257481974991957/50000000000000000000 : ℝ) ≤ (5099984817675809/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (54322257481974991957/50000000000000000000 : ℝ)^16 ≤ (5099984817675809/5000000000000000 : ℝ)^67 := by
      have hnat : (54322257481974991957 : ℕ)^16*5000000000000000^67 ≤ 5099984817675809^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54322257481974991957 50000000000000000000 5099984817675809 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5099984817675809/5000000000000000 : ℝ)) (X := (54322257481974991957/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(4062478086337/188912000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(98407683193193/4722800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (11807/25000 : ℝ)) (alpha := (4062478086337/188912000000000 : ℝ)) (beta := (98407683193193/4722800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11807/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(4062478086337/188912000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(98407683193193/4722800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (13671/25000 : ℝ) ^ (67/16 : ℝ) ≤ (7985275420679234229/100000000000000000000 : ℝ) := by
    have hpowers : (13671/25000 : ℝ)^67 ≤ (7985275420679234229/100000000000000000000 : ℝ)^16 := by
      have hnat : (13671 : ℕ)^67*100000000000000000000^16 ≤ 7985275420679234229^16*25000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13671 25000 7985275420679234229 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13671/25000 : ℝ)) (X := (7985275420679234229/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner1a : (107985275420679234229/100000000000000000000 : ℝ) ≤ (5092577603634821/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (107985275420679234229/100000000000000000000 : ℝ)^16 ≤ (5092577603634821/5000000000000000 : ℝ)^67 := by
      have hnat : (107985275420679234229 : ℕ)^16*5000000000000000^67 ≤ 5092577603634821^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107985275420679234229 100000000000000000000 5092577603634821 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5092577603634821/5000000000000000 : ℝ)) (X := (107985275420679234229/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner1b : (57985275420679234229/50000000000000000000 : ℝ) ≤ (2590040936865489/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (57985275420679234229/50000000000000000000 : ℝ)^16 ≤ (2590040936865489/2500000000000000 : ℝ)^67 := by
      have hnat : (57985275420679234229 : ℕ)^16*2500000000000000^67 ≤ 2590040936865489^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57985275420679234229 50000000000000000000 2590040936865489 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2590040936865489/2500000000000000 : ℝ)) (X := (57985275420679234229/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(10286400403869/303800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(87504270096157/2734200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (13671/25000 : ℝ)) (alpha := (10286400403869/303800000000000 : ℝ)) (beta := (87504270096157/2734200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (13671/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(10286400403869/303800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(87504270096157/2734200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (53301/100000 : ℝ) ^ (67/16 : ℝ) ≤ (896632178221562733/12500000000000000000 : ℝ) := by
    have hpowers : (53301/100000 : ℝ)^67 ≤ (896632178221562733/12500000000000000000 : ℝ)^16 := by
      have hnat : (53301 : ℕ)^67*12500000000000000000^16 ≤ 896632178221562733^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53301 100000 896632178221562733 12500000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (53301/100000 : ℝ)) (X := (896632178221562733/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner2a : (13396632178221562733/12500000000000000000 : ℝ) ≤ (2541702022121547/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (13396632178221562733/12500000000000000000 : ℝ)^16 ≤ (2541702022121547/2500000000000000 : ℝ)^67 := by
      have hnat : (13396632178221562733 : ℕ)^16*2500000000000000^67 ≤ 2541702022121547^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13396632178221562733 12500000000000000000 2541702022121547 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2541702022121547/2500000000000000 : ℝ)) (X := (13396632178221562733/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner2b : (7146632178221562733/6250000000000000000 : ℝ) ≤ (2065064480024551/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (7146632178221562733/6250000000000000000 : ℝ)^16 ≤ (2065064480024551/2000000000000000 : ℝ)^67 := by
      have hnat : (7146632178221562733 : ℕ)^16*2000000000000000^67 ≤ 2065064480024551^67*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7146632178221562733 6250000000000000000 2065064480024551 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2065064480024551/2000000000000000 : ℝ)) (X := (7146632178221562733/6250000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(41702022121547/1332525000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(158514311636567/5330100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (53301/100000 : ℝ)) (alpha := (41702022121547/1332525000000000 : ℝ)) (beta := (158514311636567/5330100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (53301/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(41702022121547/1332525000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(158514311636567/5330100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-2585403563/10000000000 : ℝ)*X 0 0+(1273161543/2500000000 : ℝ)*X 0 1+(511068457/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((4524291997/10000000000 : ℝ)*X 1 0+(-1053981647/5000000000 : ℝ)*X 1 1+(3010044073/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((908631487/2000000000 : ℝ)*X 2 0+(1202457909/2000000000 : ℝ)*X 2 1+(-1047420501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((6421641417/10000000000 : ℝ)*X 0 0+(126118509/400000000 : ℝ)*X 0 1+(1563162943/5000000000 : ℝ)*X 0 2+(6421641417/10000000000 : ℝ)*X 1 0+(126118509/400000000 : ℝ)*X 1 1+(1563162943/5000000000 : ℝ)*X 1 2+(6421641417/10000000000 : ℝ)*X 2 0+(126118509/400000000 : ℝ)*X 2 1+(1563162943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-1250252403/5000000000 : ℝ)*X 0 0+(2116948219/5000000000 : ℝ)*X 0 1+(5991322939/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((4264865849/10000000000 : ℝ)*X 1 0+(-854488379/5000000000 : ℝ)*X 1 1+(6529140991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((4283833203/10000000000 : ℝ)*X 2 0+(3399391913/5000000000 : ℝ)*X 2 1+(-1254049379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((3107468453/5000000000 : ℝ)*X 0 0+(4287165737/10000000000 : ℝ)*X 0 1+(1067483263/5000000000 : ℝ)*X 0 2+(3107468453/5000000000 : ℝ)*X 1 0+(4287165737/10000000000 : ℝ)*X 1 1+(1067483263/5000000000 : ℝ)*X 1 2+(3107468453/5000000000 : ℝ)*X 2 0+(4287165737/10000000000 : ℝ)*X 2 1+(1067483263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-431374289/2500000000 : ℝ)*X 0 0+(2463954087/5000000000 : ℝ)*X 0 1+(369625979/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((512867603/1250000000 : ℝ)*X 1 0+(-1860881389/10000000000 : ℝ)*X 1 1+(6568390749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((544248479/1000000000 : ℝ)*X 2 0+(5678195673/10000000000 : ℝ)*X 2 1+(-665678209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((918969127/1250000000 : ℝ)*X 0 0+(2977308499/10000000000 : ℝ)*X 0 1+(12832411/62500000 : ℝ)*X 0 2+(918969127/1250000000 : ℝ)*X 1 0+(2977308499/10000000000 : ℝ)*X 1 1+(12832411/62500000 : ℝ)*X 1 2+(918969127/1250000000 : ℝ)*X 2 0+(2977308499/10000000000 : ℝ)*X 2 1+(12832411/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-1638988009/10000000000 : ℝ)*X 0 0+(1097340887/2000000000 : ℝ)*X 0 1+(678656997/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((1102004877/2000000000 : ℝ)*X 1 0+(-1415022117/10000000000 : ℝ)*X 1 1+(2778473927/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((816494753/2000000000 : ℝ)*X 2 0+(6707449329/10000000000 : ℝ)*X 2 1+(-419623939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((7433928339/10000000000 : ℝ)*X 0 0+(495897549/2000000000 : ℝ)*X 0 1+(2462459827/10000000000 : ℝ)*X 0 2+(7433928339/10000000000 : ℝ)*X 1 0+(495897549/2000000000 : ℝ)*X 1 1+(2462459827/10000000000 : ℝ)*X 1 2+(7433928339/10000000000 : ℝ)*X 2 0+(495897549/2000000000 : ℝ)*X 2 1+(2462459827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306053_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((29567/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29567/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (52979570508272186668753051709/7966204447775000000000000000000000 : ℝ) := by norm_num
    linear_combination (113154295999/1000000000000 : ℝ)*(base49) + (342238946411/500000000000 : ℝ)*(base59) + (712836567363/125000000000 : ℝ)*(major_s5_0) + (712836567363/125000000000 : ℝ)*(major_s5_1) + (712836567363/125000000000 : ℝ)*(major_s5_2) + (5478001/200000000000 : ℝ)*(sp_s5_6) + (3853396030019/500000000000 : ℝ)*(sp_s5_7) + (1541328832329/200000000000 : ℝ)*(sp_s5_8) + (385338296541/50000000000 : ℝ)*(sp_s5_9) + (3698544392351/1000000000000 : ℝ)*(sp_s5_13) + (10813819/1000000000000 : ℝ)*(sp_s5_14) + (158712213/1000000000000 : ℝ)*(sp_s5_15) + (8204741/1000000000000 : ℝ)*(sp_s5_20) + (36943037/1000000000000 : ℝ)*(sp_s5_23) + (462322498387/125000000000 : ℝ)*(f.failure) + (7706802873857/1000000000000 : ℝ)*(f.sum) + (721864322737246029/1349403650000000000000000000000 : ℝ)*base62 + (292043641442963/888350000000000000000000000 : ℝ)*base64 + (38185139476121/56962500000000000000000000 : ℝ)*base66 + (115947909829681/111043750000000000000000000 : ℝ)*base68 + (602157338226889351/10488748450000000000000000000000 : ℝ)*base70 + (557630112150121/590350000000000000000000000 : ℝ)*base72 + (23672412396373/37975000000000000000000000 : ℝ)*base74 + (37449334530493/118070000000000000000000000 : ℝ)*base76 + (66852302353753999/107608998000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1009/6250000000000000 : ℝ)*base86 + (1009/6250000000000000 : ℝ)*base88 + (1009/6250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34201/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34201/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16058689811191903257123946289/1541846022150000000000000000000000 : ℝ) := by norm_num
    linear_combination (61963/100000000000 : ℝ)*(base39) + (12465135811/62500000000 : ℝ)*(base49) + (281022357459/1000000000000 : ℝ)*(base59) + (1400825390017/250000000000 : ℝ)*(major_s5_0) + (1400825390017/250000000000 : ℝ)*(major_s5_1) + (1400825390017/250000000000 : ℝ)*(major_s5_2) + (6986363/500000000000 : ℝ)*(sp_s5_1) + (19991991/1000000000000 : ℝ)*(sp_s5_2) + (11085551/200000000000 : ℝ)*(sp_s5_7) + (1893106493449/250000000000 : ℝ)*(sp_s5_14) + (302898697153/40000000000 : ℝ)*(sp_s5_15) + (189311535239/25000000000 : ℝ)*(sp_s5_16) + (3634026972159/1000000000000 : ℝ)*(sp_s5_20) + (45637339/500000000000 : ℝ)*(sp_s5_27) + (3634118246837/1000000000000 : ℝ)*(f.failure) + (7572481401551/1000000000000 : ℝ)*(f.sum) + (18563017621973791/130587450000000000000000000000 : ℝ)*base63 + (44754637975997/2665050000000000000000000000 : ℝ)*base65 + (1406374387937/11025000000000000000000000 : ℝ)*base66 + (94296909374581/333131250000000000000000000 : ℝ)*base68 + (25348090704299895293/62932490700000000000000000000000 : ℝ)*base71 + (976745878924409/1180700000000000000000000000 : ℝ)*base72 + (51616798507/153125000000000000000000 : ℝ)*base74 + (89064454122919/236140000000000000000000000 : ℝ)*base76 + (14500940606978669/104137740000000000000000000000 : ℝ)*base78 + (4841/50000000000000000 : ℝ)*base87 + (4841/50000000000000000 : ℝ)*base89 + (4841/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3293/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3293/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (741494713535252492085347139703/47797226686650000000000000000000000 : ℝ) := by norm_num
    linear_combination (234156799003/1000000000000 : ℝ)*(base40) + (5213191017/100000000000 : ℝ)*(base49) + (34762582667/100000000000 : ℝ)*(base59) + (319715127439/62500000000 : ℝ)*(major_s5_0) + (319715127439/62500000000 : ℝ)*(major_s5_1) + (319715127439/62500000000 : ℝ)*(major_s5_2) + (18969031/500000000000 : ℝ)*(sp_s5_0) + (35631383/500000000000 : ℝ)*(sp_s5_2) + (43958269/1000000000000 : ℝ)*(sp_s5_9) + (66190911/250000000000 : ℝ)*(sp_s5_20) + (6913132461597/1000000000000 : ℝ)*(sp_s5_21) + (6913170399659/1000000000000 : ℝ)*(sp_s5_22) + (54008243583/7812500000 : ℝ)*(sp_s5_23) + (3317443743629/1000000000000 : ℝ)*(sp_s5_27) + (3317708507273/1000000000000 : ℝ)*(f.failure) + (6913170399659/1000000000000 : ℝ)*(f.sum) + (100567484705562323/1012052737500000000000000000000 : ℝ)*base62 + (10077692258363/333131250000000000000000000 : ℝ)*base64 + (245827495396883/683550000000000000000000000 : ℝ)*base67 + (217156722594503/1332525000000000000000000000 : ℝ)*base69 + (1307192065144486651/3933280668750000000000000000000 : ℝ)*base70 + (178502983095139/590350000000000000000000000 : ℝ)*base73 + (3341659162081/18987500000000000000000000 : ℝ)*base75 + (17662582809183/118070000000000000000000000 : ℝ)*base77 + (162258695994753313/807067485000000000000000000000 : ℝ)*base79 + (2611/50000000000000000 : ℝ)*base86 + (2611/50000000000000000 : ℝ)*base88 + (2611/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((11807/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11807/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13671/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13671/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53301/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(53301/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29567/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29567/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34201/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34201/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3293/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3293/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306053_s5 p hpa hpb X hX hprev4

#print axioms solution
