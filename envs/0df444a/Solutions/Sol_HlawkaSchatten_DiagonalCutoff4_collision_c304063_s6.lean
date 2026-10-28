-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304063_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:48:40.02217+00:00
-- url     : https://prove2.me/submissions/654d2ba6-fca7-43f8-93f6-047a3b5a3e8d

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
theorem collision_support_c304063_s6_s6_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-667677193/5000000000 : ℝ)*x 0 + (5542977241/10000000000 : ℝ)*x 1 + (1126629203/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667677193/5000000000 : ℝ)^133 ≤ (1763996930113/25000000000000 : ℝ)^101 := by
    have hnat : (667677193 : ℕ)^133*25000000000000^101 ≤ 1763996930113^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667677193 5000000000 1763996930113 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5542977241/10000000000 : ℝ)^133 ≤ (2298914361483/5000000000000 : ℝ)^101 := by
    have hnat : (5542977241 : ℕ)^133*5000000000000^101 ≤ 2298914361483^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5542977241 10000000000 2298914361483 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126629203/2000000000 : ℝ)^133 ≤ (46965725030143/100000000000000 : ℝ)^101 := by
    have hnat : (1126629203 : ℕ)^133*100000000000000^101 ≤ 46965725030143^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126629203 2000000000 46965725030143 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-667677193/5000000000 : ℝ), (5542977241/10000000000 : ℝ), (1126629203/2000000000 : ℝ)] ![(1763996930113/25000000000000 : ℝ), (2298914361483/5000000000000 : ℝ), (46965725030143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-667677193/5000000000 : ℝ)|^133 ≤ (1763996930113/25000000000000 : ℝ)^101
        have hw : |(-667677193/5000000000 : ℝ)|=(667677193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5542977241/10000000000 : ℝ)|^133 ≤ (2298914361483/5000000000000 : ℝ)^101
        have hw : |(5542977241/10000000000 : ℝ)|=(5542977241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126629203/2000000000 : ℝ)|^133 ≤ (46965725030143/100000000000000 : ℝ)^101
        have hw : |(1126629203/2000000000 : ℝ)|=(1126629203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (554453819/1000000000 : ℝ)*x 0 + (-13535837/100000000 : ℝ)*x 1 + (2810005007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (554453819/1000000000 : ℝ)^133 ≤ (45995338158713/100000000000000 : ℝ)^101 := by
    have hnat : (554453819 : ℕ)^133*100000000000000^101 ≤ 45995338158713^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554453819 1000000000 45995338158713 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13535837/100000000 : ℝ)^133 ≤ (7183102824763/100000000000000 : ℝ)^101 := by
    have hnat : (13535837 : ℕ)^133*100000000000000^101 ≤ 7183102824763^101*100000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13535837 100000000 7183102824763 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2810005007/5000000000 : ℝ)^133 ≤ (2926347438029/6250000000000 : ℝ)^101 := by
    have hnat : (2810005007 : ℕ)^133*6250000000000^101 ≤ 2926347438029^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2810005007 5000000000 2926347438029 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(554453819/1000000000 : ℝ), (-13535837/100000000 : ℝ), (2810005007/5000000000 : ℝ)] ![(45995338158713/100000000000000 : ℝ), (7183102824763/100000000000000 : ℝ), (2926347438029/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(554453819/1000000000 : ℝ)|^133 ≤ (45995338158713/100000000000000 : ℝ)^101
        have hw : |(554453819/1000000000 : ℝ)|=(554453819/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13535837/100000000 : ℝ)|^133 ≤ (7183102824763/100000000000000 : ℝ)^101
        have hw : |(-13535837/100000000 : ℝ)|=(13535837/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2810005007/5000000000 : ℝ)|^133 ≤ (2926347438029/6250000000000 : ℝ)^101
        have hw : |(2810005007/5000000000 : ℝ)|=(2810005007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1397883861/2500000000 : ℝ)*x 0 + (5605798203/10000000000 : ℝ)*x 1 + (-651003281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1397883861/2500000000 : ℝ)^133 ≤ (46509420681219/100000000000000 : ℝ)^101 := by
    have hnat : (1397883861 : ℕ)^133*100000000000000^101 ≤ 46509420681219^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397883861 2500000000 46509420681219 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5605798203/10000000000 : ℝ)^133 ≤ (46665706298677/100000000000000 : ℝ)^101 := by
    have hnat : (5605798203 : ℕ)^133*100000000000000^101 ≤ 46665706298677^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5605798203 10000000000 46665706298677 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651003281/5000000000 : ℝ)^133 ≤ (6824873002267/100000000000000 : ℝ)^101 := by
    have hnat : (651003281 : ℕ)^133*100000000000000^101 ≤ 6824873002267^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651003281 5000000000 6824873002267 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1397883861/2500000000 : ℝ), (5605798203/10000000000 : ℝ), (-651003281/5000000000 : ℝ)] ![(46509420681219/100000000000000 : ℝ), (46665706298677/100000000000000 : ℝ), (6824873002267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1397883861/2500000000 : ℝ)|^133 ≤ (46509420681219/100000000000000 : ℝ)^101
        have hw : |(1397883861/2500000000 : ℝ)|=(1397883861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5605798203/10000000000 : ℝ)|^133 ≤ (46665706298677/100000000000000 : ℝ)^101
        have hw : |(5605798203/10000000000 : ℝ)|=(5605798203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-651003281/5000000000 : ℝ)|^133 ≤ (6824873002267/100000000000000 : ℝ)^101
        have hw : |(-651003281/5000000000 : ℝ)|=(651003281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2210550093/5000000000 : ℝ)*x 0 + (4356793869/10000000000 : ℝ)*x 1 + (530886371/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210550093/5000000000 : ℝ)^133 ≤ (17068413166691/50000000000000 : ℝ)^101 := by
    have hnat : (2210550093 : ℕ)^133*50000000000000^101 ≤ 17068413166691^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210550093 5000000000 17068413166691 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4356793869/10000000000 : ℝ)^133 ≤ (6696898024203/20000000000000 : ℝ)^101 := by
    have hnat : (4356793869 : ℕ)^133*20000000000000^101 ≤ 6696898024203^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356793869 10000000000 6696898024203 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530886371/1250000000 : ℝ)^133 ≤ (16189341771921/50000000000000 : ℝ)^101 := by
    have hnat : (530886371 : ℕ)^133*50000000000000^101 ≤ 16189341771921^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530886371 1250000000 16189341771921 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2210550093/5000000000 : ℝ), (4356793869/10000000000 : ℝ), (530886371/1250000000 : ℝ)] ![(17068413166691/50000000000000 : ℝ), (6696898024203/20000000000000 : ℝ), (16189341771921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2210550093/5000000000 : ℝ)|^133 ≤ (17068413166691/50000000000000 : ℝ)^101
        have hw : |(2210550093/5000000000 : ℝ)|=(2210550093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4356793869/10000000000 : ℝ)|^133 ≤ (6696898024203/20000000000000 : ℝ)^101
        have hw : |(4356793869/10000000000 : ℝ)|=(4356793869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530886371/1250000000 : ℝ)|^133 ≤ (16189341771921/50000000000000 : ℝ)^101
        have hw : |(530886371/1250000000 : ℝ)|=(530886371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-105629611/1000000000 : ℝ)*x 0 + (446384321/1000000000 : ℝ)*x 1 + (1701444631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105629611/1000000000 : ℝ)^133 ≤ (2590956125061/50000000000000 : ℝ)^101 := by
    have hnat : (105629611 : ℕ)^133*50000000000000^101 ≤ 2590956125061^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105629611 1000000000 2590956125061 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (446384321/1000000000 : ℝ)^133 ≤ (34572089061859/100000000000000 : ℝ)^101 := by
    have hnat : (446384321 : ℕ)^133*100000000000000^101 ≤ 34572089061859^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446384321 1000000000 34572089061859 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1701444631/2500000000 : ℝ)^133 ≤ (30122999338127/50000000000000 : ℝ)^101 := by
    have hnat : (1701444631 : ℕ)^133*50000000000000^101 ≤ 30122999338127^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701444631 2500000000 30122999338127 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105629611/1000000000 : ℝ), (446384321/1000000000 : ℝ), (1701444631/2500000000 : ℝ)] ![(2590956125061/50000000000000 : ℝ), (34572089061859/100000000000000 : ℝ), (30122999338127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105629611/1000000000 : ℝ)|^133 ≤ (2590956125061/50000000000000 : ℝ)^101
        have hw : |(-105629611/1000000000 : ℝ)|=(105629611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(446384321/1000000000 : ℝ)|^133 ≤ (34572089061859/100000000000000 : ℝ)^101
        have hw : |(446384321/1000000000 : ℝ)|=(446384321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1701444631/2500000000 : ℝ)|^133 ≤ (30122999338127/50000000000000 : ℝ)^101
        have hw : |(1701444631/2500000000 : ℝ)|=(1701444631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4856658339/10000000000 : ℝ)*x 0 + (-91160149/2500000000 : ℝ)*x 1 + (84904723/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4856658339/10000000000 : ℝ)^133 ≤ (19316540789001/50000000000000 : ℝ)^101 := by
    have hnat : (4856658339 : ℕ)^133*50000000000000^101 ≤ 19316540789001^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4856658339 10000000000 19316540789001 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91160149/2500000000 : ℝ)^133 ≤ (39908767187/3125000000000 : ℝ)^101 := by
    have hnat : (91160149 : ℕ)^133*3125000000000^101 ≤ 39908767187^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91160149 2500000000 39908767187 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84904723/125000000 : ℝ)^133 ≤ (60089837856241/100000000000000 : ℝ)^101 := by
    have hnat : (84904723 : ℕ)^133*100000000000000^101 ≤ 60089837856241^101*125000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84904723 125000000 60089837856241 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4856658339/10000000000 : ℝ), (-91160149/2500000000 : ℝ), (84904723/125000000 : ℝ)] ![(19316540789001/50000000000000 : ℝ), (39908767187/3125000000000 : ℝ), (60089837856241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4856658339/10000000000 : ℝ)|^133 ≤ (19316540789001/50000000000000 : ℝ)^101
        have hw : |(4856658339/10000000000 : ℝ)|=(4856658339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91160149/2500000000 : ℝ)|^133 ≤ (39908767187/3125000000000 : ℝ)^101
        have hw : |(-91160149/2500000000 : ℝ)|=(91160149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84904723/125000000 : ℝ)|^133 ≤ (60089837856241/100000000000000 : ℝ)^101
        have hw : |(84904723/125000000 : ℝ)|=(84904723/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1149389353/2500000000 : ℝ)*x 0 + (282149119/400000000 : ℝ)*x 1 + (-280705793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1149389353/2500000000 : ℝ)^133 ≤ (224638965781/625000000000 : ℝ)^101 := by
    have hnat : (1149389353 : ℕ)^133*625000000000^101 ≤ 224638965781^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149389353 2500000000 224638965781 625000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282149119/400000000 : ℝ)^133 ≤ (12630569902387/20000000000000 : ℝ)^101 := by
    have hnat : (282149119 : ℕ)^133*20000000000000^101 ≤ 12630569902387^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282149119 400000000 12630569902387 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280705793/10000000000 : ℝ)^133 ≤ (904915957611/100000000000000 : ℝ)^101 := by
    have hnat : (280705793 : ℕ)^133*100000000000000^101 ≤ 904915957611^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280705793 10000000000 904915957611 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1149389353/2500000000 : ℝ), (282149119/400000000 : ℝ), (-280705793/10000000000 : ℝ)] ![(224638965781/625000000000 : ℝ), (12630569902387/20000000000000 : ℝ), (904915957611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1149389353/2500000000 : ℝ)|^133 ≤ (224638965781/625000000000 : ℝ)^101
        have hw : |(1149389353/2500000000 : ℝ)|=(1149389353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282149119/400000000 : ℝ)|^133 ≤ (12630569902387/20000000000000 : ℝ)^101
        have hw : |(282149119/400000000 : ℝ)|=(282149119/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-280705793/10000000000 : ℝ)|^133 ≤ (904915957611/100000000000000 : ℝ)^101
        have hw : |(-280705793/10000000000 : ℝ)|=(280705793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4418893997/10000000000 : ℝ)*x 0 + (6172633363/10000000000 : ℝ)*x 1 + (105628413/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4418893997/10000000000 : ℝ)^133 ≤ (34114396221941/100000000000000 : ℝ)^101 := by
    have hnat : (4418893997 : ℕ)^133*100000000000000^101 ≤ 34114396221941^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418893997 10000000000 34114396221941 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6172633363/10000000000 : ℝ)^133 ≤ (26488349391887/50000000000000 : ℝ)^101 := by
    have hnat : (6172633363 : ℕ)^133*50000000000000^101 ≤ 26488349391887^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6172633363 10000000000 26488349391887 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105628413/500000000 : ℝ)^133 ≤ (1613613122773/12500000000000 : ℝ)^101 := by
    have hnat : (105628413 : ℕ)^133*12500000000000^101 ≤ 1613613122773^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105628413 500000000 1613613122773 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4418893997/10000000000 : ℝ), (6172633363/10000000000 : ℝ), (105628413/500000000 : ℝ)] ![(34114396221941/100000000000000 : ℝ), (26488349391887/50000000000000 : ℝ), (1613613122773/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4418893997/10000000000 : ℝ)|^133 ≤ (34114396221941/100000000000000 : ℝ)^101
        have hw : |(4418893997/10000000000 : ℝ)|=(4418893997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6172633363/10000000000 : ℝ)|^133 ≤ (26488349391887/50000000000000 : ℝ)^101
        have hw : |(6172633363/10000000000 : ℝ)|=(6172633363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105628413/500000000 : ℝ)|^133 ≤ (1613613122773/12500000000000 : ℝ)^101
        have hw : |(105628413/500000000 : ℝ)|=(105628413/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-66281289/2000000000 : ℝ)*x 0 + (974514971/2000000000 : ℝ)*x 1 + (6791021679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66281289/2000000000 : ℝ)^133 ≤ (1126067487399/100000000000000 : ℝ)^101 := by
    have hnat : (66281289 : ℕ)^133*100000000000000^101 ≤ 1126067487399^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66281289 2000000000 1126067487399 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974514971/2000000000 : ℝ)^133 ≤ (38799892822353/100000000000000 : ℝ)^101 := by
    have hnat : (974514971 : ℕ)^133*100000000000000^101 ≤ 38799892822353^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974514971 2000000000 38799892822353 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6791021679/10000000000 : ℝ)^133 ≤ (60074039679193/100000000000000 : ℝ)^101 := by
    have hnat : (6791021679 : ℕ)^133*100000000000000^101 ≤ 60074039679193^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6791021679 10000000000 60074039679193 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66281289/2000000000 : ℝ), (974514971/2000000000 : ℝ), (6791021679/10000000000 : ℝ)] ![(1126067487399/100000000000000 : ℝ), (38799892822353/100000000000000 : ℝ), (60074039679193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66281289/2000000000 : ℝ)|^133 ≤ (1126067487399/100000000000000 : ℝ)^101
        have hw : |(-66281289/2000000000 : ℝ)|=(66281289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(974514971/2000000000 : ℝ)|^133 ≤ (38799892822353/100000000000000 : ℝ)^101
        have hw : |(974514971/2000000000 : ℝ)|=(974514971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6791021679/10000000000 : ℝ)|^133 ≤ (60074039679193/100000000000000 : ℝ)^101
        have hw : |(6791021679/10000000000 : ℝ)|=(6791021679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (900106037/2000000000 : ℝ)*x 0 + (-524535917/5000000000 : ℝ)*x 1 + (6777619553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (900106037/2000000000 : ℝ)^133 ≤ (34946736597621/100000000000000 : ℝ)^101 := by
    have hnat : (900106037 : ℕ)^133*100000000000000^101 ≤ 34946736597621^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900106037 2000000000 34946736597621 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524535917/5000000000 : ℝ)^133 ≤ (5135293841379/100000000000000 : ℝ)^101 := by
    have hnat : (524535917 : ℕ)^133*100000000000000^101 ≤ 5135293841379^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524535917 5000000000 5135293841379 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6777619553/10000000000 : ℝ)^133 ≤ (29958984768479/50000000000000 : ℝ)^101 := by
    have hnat : (6777619553 : ℕ)^133*50000000000000^101 ≤ 29958984768479^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6777619553 10000000000 29958984768479 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(900106037/2000000000 : ℝ), (-524535917/5000000000 : ℝ), (6777619553/10000000000 : ℝ)] ![(34946736597621/100000000000000 : ℝ), (5135293841379/100000000000000 : ℝ), (29958984768479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(900106037/2000000000 : ℝ)|^133 ≤ (34946736597621/100000000000000 : ℝ)^101
        have hw : |(900106037/2000000000 : ℝ)|=(900106037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524535917/5000000000 : ℝ)|^133 ≤ (5135293841379/100000000000000 : ℝ)^101
        have hw : |(-524535917/5000000000 : ℝ)|=(524535917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6777619553/10000000000 : ℝ)|^133 ≤ (29958984768479/50000000000000 : ℝ)^101
        have hw : |(6777619553/10000000000 : ℝ)|=(6777619553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3373313323/5000000000 : ℝ)*x 0 + (2468387981/5000000000 : ℝ)*x 1 + (-147731687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3373313323/5000000000 : ℝ)^133 ≤ (59557426234959/100000000000000 : ℝ)^101 := by
    have hnat : (3373313323 : ℕ)^133*100000000000000^101 ≤ 59557426234959^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3373313323 5000000000 59557426234959 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2468387981/5000000000 : ℝ)^133 ≤ (4934311856603/12500000000000 : ℝ)^101 := by
    have hnat : (2468387981 : ℕ)^133*12500000000000^101 ≤ 4934311856603^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2468387981 5000000000 4934311856603 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147731687/5000000000 : ℝ)^133 ≤ (968078891903/100000000000000 : ℝ)^101 := by
    have hnat : (147731687 : ℕ)^133*100000000000000^101 ≤ 968078891903^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147731687 5000000000 968078891903 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3373313323/5000000000 : ℝ), (2468387981/5000000000 : ℝ), (-147731687/5000000000 : ℝ)] ![(59557426234959/100000000000000 : ℝ), (4934311856603/12500000000000 : ℝ), (968078891903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3373313323/5000000000 : ℝ)|^133 ≤ (59557426234959/100000000000000 : ℝ)^101
        have hw : |(3373313323/5000000000 : ℝ)|=(3373313323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2468387981/5000000000 : ℝ)|^133 ≤ (4934311856603/12500000000000 : ℝ)^101
        have hw : |(2468387981/5000000000 : ℝ)|=(2468387981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147731687/5000000000 : ℝ)|^133 ≤ (968078891903/100000000000000 : ℝ)^101
        have hw : |(-147731687/5000000000 : ℝ)|=(147731687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6790085169/10000000000 : ℝ)*x 0 + (1838754193/5000000000 : ℝ)*x 1 + (133910989/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6790085169/10000000000 : ℝ)^133 ≤ (3003156533989/5000000000000 : ℝ)^101 := by
    have hnat : (6790085169 : ℕ)^133*5000000000000^101 ≤ 3003156533989^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6790085169 10000000000 3003156533989 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1838754193/5000000000 : ℝ)^133 ≤ (26785965819609/100000000000000 : ℝ)^101 := by
    have hnat : (1838754193 : ℕ)^133*100000000000000^101 ≤ 26785965819609^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838754193 5000000000 26785965819609 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133910989/625000000 : ℝ)^133 ≤ (821931467583/6250000000000 : ℝ)^101 := by
    have hnat : (133910989 : ℕ)^133*6250000000000^101 ≤ 821931467583^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133910989 625000000 821931467583 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6790085169/10000000000 : ℝ), (1838754193/5000000000 : ℝ), (133910989/625000000 : ℝ)] ![(3003156533989/5000000000000 : ℝ), (26785965819609/100000000000000 : ℝ), (821931467583/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6790085169/10000000000 : ℝ)|^133 ≤ (3003156533989/5000000000000 : ℝ)^101
        have hw : |(6790085169/10000000000 : ℝ)|=(6790085169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1838754193/5000000000 : ℝ)|^133 ≤ (26785965819609/100000000000000 : ℝ)^101
        have hw : |(1838754193/5000000000 : ℝ)|=(1838754193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(133910989/625000000 : ℝ)|^133 ≤ (821931467583/6250000000000 : ℝ)^101
        have hw : |(133910989/625000000 : ℝ)|=(133910989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-139620761/5000000000 : ℝ)*x 0 + (6343629939/10000000000 : ℝ)*x 1 + (215115593/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139620761/5000000000 : ℝ)^133 ≤ (44935256739/5000000000000 : ℝ)^101 := by
    have hnat : (139620761 : ℕ)^133*5000000000000^101 ≤ 44935256739^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139620761 5000000000 44935256739 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6343629939/10000000000 : ℝ)^133 ≤ (6864710365719/12500000000000 : ℝ)^101 := by
    have hnat : (6343629939 : ℕ)^133*12500000000000^101 ≤ 6864710365719^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6343629939 10000000000 6864710365719 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215115593/400000000 : ℝ)^133 ≤ (44183611934879/100000000000000 : ℝ)^101 := by
    have hnat : (215115593 : ℕ)^133*100000000000000^101 ≤ 44183611934879^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215115593 400000000 44183611934879 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-139620761/5000000000 : ℝ), (6343629939/10000000000 : ℝ), (215115593/400000000 : ℝ)] ![(44935256739/5000000000000 : ℝ), (6864710365719/12500000000000 : ℝ), (44183611934879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-139620761/5000000000 : ℝ)|^133 ≤ (44935256739/5000000000000 : ℝ)^101
        have hw : |(-139620761/5000000000 : ℝ)|=(139620761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6343629939/10000000000 : ℝ)|^133 ≤ (6864710365719/12500000000000 : ℝ)^101
        have hw : |(6343629939/10000000000 : ℝ)|=(6343629939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215115593/400000000 : ℝ)|^133 ≤ (44183611934879/100000000000000 : ℝ)^101
        have hw : |(215115593/400000000 : ℝ)|=(215115593/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3375394431/5000000000 : ℝ)*x 0 + (-139077057/5000000000 : ℝ)*x 1 + (617400769/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3375394431/5000000000 : ℝ)^133 ≤ (59605815225499/100000000000000 : ℝ)^101 := by
    have hnat : (3375394431 : ℕ)^133*100000000000000^101 ≤ 59605815225499^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3375394431 5000000000 59605815225499 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139077057/5000000000 : ℝ)^133 ≤ (894099475751/100000000000000 : ℝ)^101 := by
    have hnat : (139077057 : ℕ)^133*100000000000000^101 ≤ 894099475751^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139077057 5000000000 894099475751 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (617400769/1250000000 : ℝ)^133 ≤ (39500085279151/100000000000000 : ℝ)^101 := by
    have hnat : (617400769 : ℕ)^133*100000000000000^101 ≤ 39500085279151^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617400769 1250000000 39500085279151 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3375394431/5000000000 : ℝ), (-139077057/5000000000 : ℝ), (617400769/1250000000 : ℝ)] ![(59605815225499/100000000000000 : ℝ), (894099475751/100000000000000 : ℝ), (39500085279151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3375394431/5000000000 : ℝ)|^133 ≤ (59605815225499/100000000000000 : ℝ)^101
        have hw : |(3375394431/5000000000 : ℝ)|=(3375394431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-139077057/5000000000 : ℝ)|^133 ≤ (894099475751/100000000000000 : ℝ)^101
        have hw : |(-139077057/5000000000 : ℝ)|=(139077057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(617400769/1250000000 : ℝ)|^133 ≤ (39500085279151/100000000000000 : ℝ)^101
        have hw : |(617400769/1250000000 : ℝ)|=(617400769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4471008961/10000000000 : ℝ)*x 0 + (6833112007/10000000000 : ℝ)*x 1 + (-199011379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4471008961/10000000000 : ℝ)^133 ≤ (4330648668131/12500000000000 : ℝ)^101 := by
    have hnat : (4471008961 : ℕ)^133*12500000000000^101 ≤ 4330648668131^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4471008961 10000000000 4330648668131 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6833112007/10000000000 : ℝ)^133 ≤ (15141205780063/25000000000000 : ℝ)^101 := by
    have hnat : (6833112007 : ℕ)^133*25000000000000^101 ≤ 15141205780063^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6833112007 10000000000 15141205780063 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199011379/2000000000 : ℝ)^133 ≤ (2394993755063/50000000000000 : ℝ)^101 := by
    have hnat : (199011379 : ℕ)^133*50000000000000^101 ≤ 2394993755063^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199011379 2000000000 2394993755063 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4471008961/10000000000 : ℝ), (6833112007/10000000000 : ℝ), (-199011379/2000000000 : ℝ)] ![(4330648668131/12500000000000 : ℝ), (15141205780063/25000000000000 : ℝ), (2394993755063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4471008961/10000000000 : ℝ)|^133 ≤ (4330648668131/12500000000000 : ℝ)^101
        have hw : |(4471008961/10000000000 : ℝ)|=(4471008961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6833112007/10000000000 : ℝ)|^133 ≤ (15141205780063/25000000000000 : ℝ)^101
        have hw : |(6833112007/10000000000 : ℝ)|=(6833112007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199011379/2000000000 : ℝ)|^133 ≤ (2394993755063/50000000000000 : ℝ)^101
        have hw : |(-199011379/2000000000 : ℝ)|=(199011379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s6_s6_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3473863451/5000000000 : ℝ)*x 0 + (2974676209/10000000000 : ℝ)*x 1 + (2700374057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3473863451/5000000000 : ℝ)^133 ≤ (15476527243839/25000000000000 : ℝ)^101 := by
    have hnat : (3473863451 : ℕ)^133*25000000000000^101 ≤ 15476527243839^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3473863451 5000000000 15476527243839 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2974676209/10000000000 : ℝ)^133 ≤ (10129283310027/50000000000000 : ℝ)^101 := by
    have hnat : (2974676209 : ℕ)^133*50000000000000^101 ≤ 10129283310027^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2974676209 10000000000 10129283310027 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700374057/10000000000 : ℝ)^133 ≤ (8917662195929/50000000000000 : ℝ)^101 := by
    have hnat : (2700374057 : ℕ)^133*50000000000000^101 ≤ 8917662195929^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700374057 10000000000 8917662195929 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3473863451/5000000000 : ℝ), (2974676209/10000000000 : ℝ), (2700374057/10000000000 : ℝ)] ![(15476527243839/25000000000000 : ℝ), (10129283310027/50000000000000 : ℝ), (8917662195929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3473863451/5000000000 : ℝ)|^133 ≤ (15476527243839/25000000000000 : ℝ)^101
        have hw : |(3473863451/5000000000 : ℝ)|=(3473863451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2974676209/10000000000 : ℝ)|^133 ≤ (10129283310027/50000000000000 : ℝ)^101
        have hw : |(2974676209/10000000000 : ℝ)|=(2974676209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700374057/10000000000 : ℝ)|^133 ≤ (8917662195929/50000000000000 : ℝ)^101
        have hw : |(2700374057/10000000000 : ℝ)|=(2700374057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304063_s6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((31691/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31691/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4017/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4017/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3147/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3147/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64/125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64/125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12231/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12231/25000 : ℝ)*X 1 2) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (31691/50000 : ℝ) ^ (33/8 : ℝ) ≤ (762218531061101559/5000000000000000000 : ℝ) := by
    have hpowers : (31691/50000 : ℝ)^33 ≤ (762218531061101559/5000000000000000000 : ℝ)^8 := by
      have hnat : (31691 : ℕ)^33*5000000000000000000^8 ≤ 762218531061101559^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31691 50000 762218531061101559 5000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31691/50000 : ℝ)) (X := (762218531061101559/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner0a : (5762218531061101559/5000000000000000000 : ℝ) ≤ (10349946718466493/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (5762218531061101559/5000000000000000000 : ℝ)^8 ≤ (10349946718466493/10000000000000000 : ℝ)^33 := by
      have hnat : (5762218531061101559 : ℕ)^8*10000000000000000^33 ≤ 10349946718466493^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5762218531061101559 5000000000000000000 10349946718466493 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10349946718466493/10000000000000000 : ℝ)) (X := (5762218531061101559/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner0b : (3262218531061101559/2500000000000000000 : ℝ) ≤ (2133279218906877/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3262218531061101559/2500000000000000000 : ℝ)^8 ≤ (2133279218906877/2000000000000000 : ℝ)^33 := by
      have hnat : (3262218531061101559 : ℕ)^8*2000000000000000^33 ≤ 2133279218906877^33*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3262218531061101559 2500000000000000000 2133279218906877 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2133279218906877/2000000000000000 : ℝ)) (X := (3262218531061101559/2500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(349946718466493/6338200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(79112344016973/1584550000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (31691/50000 : ℝ)) (alpha := (349946718466493/6338200000000000 : ℝ)) (beta := (79112344016973/1584550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (31691/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(349946718466493/6338200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(79112344016973/1584550000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (4017/6250 : ℝ) ^ (33/8 : ℝ) ≤ (8073465405591262077/50000000000000000000 : ℝ) := by
    have hpowers : (4017/6250 : ℝ)^33 ≤ (8073465405591262077/50000000000000000000 : ℝ)^8 := by
      have hnat : (4017 : ℕ)^33*50000000000000000000^8 ≤ 8073465405591262077^8*6250^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4017 6250 8073465405591262077 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4017/6250 : ℝ)) (X := (8073465405591262077/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner1a : (58073465405591262077/50000000000000000000 : ℝ) ≤ (1036953905526989/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (58073465405591262077/50000000000000000000 : ℝ)^8 ≤ (1036953905526989/1000000000000000 : ℝ)^33 := by
      have hnat : (58073465405591262077 : ℕ)^8*1000000000000000^33 ≤ 1036953905526989^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58073465405591262077 50000000000000000000 1036953905526989 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1036953905526989/1000000000000000 : ℝ)) (X := (58073465405591262077/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner1b : (33073465405591262077/25000000000000000000 : ℝ) ≤ (535099040803569/500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (33073465405591262077/25000000000000000000 : ℝ)^8 ≤ (535099040803569/500000000000000 : ℝ)^33 := by
      have hnat : (33073465405591262077 : ℕ)^8*500000000000000^33 ≤ 535099040803569^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33073465405591262077 25000000000000000000 535099040803569 500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (535099040803569/500000000000000 : ℝ)) (X := (33073465405591262077/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(36953905526989/642720000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(33244176080149/642720000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (4017/6250 : ℝ)) (alpha := (36953905526989/642720000000000 : ℝ)) (beta := (33244176080149/642720000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (4017/6250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(36953905526989/642720000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(33244176080149/642720000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (61709/100000 : ℝ) ^ (33/8 : ℝ) ≤ (6825863554093951497/50000000000000000000 : ℝ) := by
    have hpowers : (61709/100000 : ℝ)^33 ≤ (6825863554093951497/50000000000000000000 : ℝ)^8 := by
      have hnat : (61709 : ℕ)^33*50000000000000000000^8 ≤ 6825863554093951497^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61709 100000 6825863554093951497 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61709/100000 : ℝ)) (X := (6825863554093951497/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner2a : (56825863554093951497/50000000000000000000 : ℝ) ≤ (2578772249310683/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (56825863554093951497/50000000000000000000 : ℝ)^8 ≤ (2578772249310683/2500000000000000 : ℝ)^33 := by
      have hnat : (56825863554093951497 : ℕ)^8*2500000000000000^33 ≤ 2578772249310683^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56825863554093951497 50000000000000000000 2578772249310683 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2578772249310683/2500000000000000 : ℝ)) (X := (56825863554093951497/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner2b : (31825863554093951497/25000000000000000000 : ℝ) ≤ (5301341818448117/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (31825863554093951497/25000000000000000000 : ℝ)^8 ≤ (5301341818448117/5000000000000000 : ℝ)^33 := by
      have hnat : (31825863554093951497 : ℕ)^8*5000000000000000^33 ≤ 5301341818448117^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31825863554093951497 25000000000000000000 5301341818448117 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5301341818448117/5000000000000000 : ℝ)) (X := (31825863554093951497/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(78772249310683/1542725000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(143797319826751/3085450000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (61709/100000 : ℝ)) (alpha := (78772249310683/1542725000000000 : ℝ)) (beta := (143797319826751/3085450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (61709/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(78772249310683/1542725000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(143797319826751/3085450000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-667677193/5000000000 : ℝ)*X 0 0+(5542977241/10000000000 : ℝ)*X 0 1+(1126629203/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((554453819/1000000000 : ℝ)*X 1 0+(-13535837/100000000 : ℝ)*X 1 1+(2810005007/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((1397883861/2500000000 : ℝ)*X 2 0+(5605798203/10000000000 : ℝ)*X 2 1+(-651003281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((2210550093/5000000000 : ℝ)*X 0 0+(4356793869/10000000000 : ℝ)*X 0 1+(530886371/1250000000 : ℝ)*X 0 2+(2210550093/5000000000 : ℝ)*X 1 0+(4356793869/10000000000 : ℝ)*X 1 1+(530886371/1250000000 : ℝ)*X 1 2+(2210550093/5000000000 : ℝ)*X 2 0+(4356793869/10000000000 : ℝ)*X 2 1+(530886371/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-105629611/1000000000 : ℝ)*X 0 0+(446384321/1000000000 : ℝ)*X 0 1+(1701444631/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((4856658339/10000000000 : ℝ)*X 1 0+(-91160149/2500000000 : ℝ)*X 1 1+(84904723/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((1149389353/2500000000 : ℝ)*X 2 0+(282149119/400000000 : ℝ)*X 2 1+(-280705793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((4418893997/10000000000 : ℝ)*X 0 0+(6172633363/10000000000 : ℝ)*X 0 1+(105628413/500000000 : ℝ)*X 0 2+(4418893997/10000000000 : ℝ)*X 1 0+(6172633363/10000000000 : ℝ)*X 1 1+(105628413/500000000 : ℝ)*X 1 2+(4418893997/10000000000 : ℝ)*X 2 0+(6172633363/10000000000 : ℝ)*X 2 1+(105628413/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-66281289/2000000000 : ℝ)*X 0 0+(974514971/2000000000 : ℝ)*X 0 1+(6791021679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((900106037/2000000000 : ℝ)*X 1 0+(-524535917/5000000000 : ℝ)*X 1 1+(6777619553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((3373313323/5000000000 : ℝ)*X 2 0+(2468387981/5000000000 : ℝ)*X 2 1+(-147731687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((6790085169/10000000000 : ℝ)*X 0 0+(1838754193/5000000000 : ℝ)*X 0 1+(133910989/625000000 : ℝ)*X 0 2+(6790085169/10000000000 : ℝ)*X 1 0+(1838754193/5000000000 : ℝ)*X 1 1+(133910989/625000000 : ℝ)*X 1 2+(6790085169/10000000000 : ℝ)*X 2 0+(1838754193/5000000000 : ℝ)*X 2 1+(133910989/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-139620761/5000000000 : ℝ)*X 0 0+(6343629939/10000000000 : ℝ)*X 0 1+(215115593/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((3375394431/5000000000 : ℝ)*X 1 0+(-139077057/5000000000 : ℝ)*X 1 1+(617400769/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((4471008961/10000000000 : ℝ)*X 2 0+(6833112007/10000000000 : ℝ)*X 2 1+(-199011379/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((3473863451/5000000000 : ℝ)*X 0 0+(2974676209/10000000000 : ℝ)*X 0 1+(2700374057/10000000000 : ℝ)*X 0 2+(3473863451/5000000000 : ℝ)*X 1 0+(2974676209/10000000000 : ℝ)*X 1 1+(2700374057/10000000000 : ℝ)*X 1 2+(3473863451/5000000000 : ℝ)*X 2 0+(2974676209/10000000000 : ℝ)*X 2 1+(2700374057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((3147/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3147/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16859664750340304455891356631333/1047430028616400000000000000000000000 : ℝ) := by norm_num
    linear_combination (1667317/500000000000 : ℝ)*(base50) + (34606335523/250000000000 : ℝ)*(base60) + (3362037879193/1000000000000 : ℝ)*(major_s6_0) + (3362037879193/1000000000000 : ℝ)*(major_s6_1) + (3362037879193/1000000000000 : ℝ)*(major_s6_2) + (21526603/1000000000000 : ℝ)*(sp_s6_0) + (14361063/1000000000000 : ℝ)*(sp_s6_6) + (281709516577/62500000000 : ℝ)*(sp_s6_7) + (901462750287/200000000000 : ℝ)*(sp_s6_8) + (14085392501/3125000000 : ℝ)*(sp_s6_9) + (2216635962789/1000000000000 : ℝ)*(sp_s6_13) + (23138643/500000000000 : ℝ)*(sp_s6_14) + (106317687/1000000000000 : ℝ)*(sp_s6_15) + (47234401/500000000000 : ℝ)*(sp_s6_23) + (554162580963/250000000000 : ℝ)*(f.failure) + (4507420069121/1000000000000 : ℝ)*(f.sum) + (12168580381001793781/198308042400000000000000000000000 : ℝ)*base63 + (32451938947517/192840625000000000000000000 : ℝ)*base64 + (17765996783461/25708800000000000000000000 : ℝ)*base67 + (577612464818143/3085450000000000000000000000 : ℝ)*base69 + (132957674268234646587/391123983800000000000000000000000 : ℝ)*base70 + (3817710920587/12379296875000000000000000 : ℝ)*base72 + (357147259592459/642720000000000000000000000 : ℝ)*base74 + (2403312592773611/6338200000000000000000000000 : ℝ)*base76 + (49537640422913567803/101842197600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (19/97656250000000 : ℝ)*base86 + (19/97656250000000 : ℝ)*base88 + (19/97656250000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64/125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64/125 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (369821037443351954299474215003/104743002861640000000000000000000000 : ℝ) := by norm_num
    linear_combination (871893/500000000000 : ℝ)*(base21) + (8043/25000000000 : ℝ)*(base39) + (75527/1000000000000 : ℝ)*(base49) + (678669329451/200000000000 : ℝ)*(major_s6_0) + (678669329451/200000000000 : ℝ)*(major_s6_1) + (678669329451/200000000000 : ℝ)*(major_s6_2) + (2814039/500000000000 : ℝ)*(sp_s6_2) + (13161973/1000000000000 : ℝ)*(sp_s6_7) + (6768067/500000000000 : ℝ)*(sp_s6_8) + (4549386213871/1000000000000 : ℝ)*(sp_s6_14) + (454938583971/100000000000 : ℝ)*(sp_s6_15) + (227469600199/50000000000 : ℝ)*(sp_s6_16) + (559319052851/250000000000 : ℝ)*(sp_s6_20) + (16530339/1000000000000 : ℝ)*(sp_s6_27) + (1118646370871/500000000000 : ℝ)*(f.failure) + (1137349843961/250000000000 : ℝ)*(f.sum) + (1200705131274849839/2644107232000000000000000000000 : ℝ)*base62 + (482372584919769/617090000000000000000000000 : ℝ)*base64 + (34324694521171/42848000000000000000000000 : ℝ)*base66 + (156293047598601/154272500000000000000000000 : ℝ)*base68 + (3642961938004088593/15644959352000000000000000000000 : ℝ)*base70 + (94313453875449/79227500000000000000000000 : ℝ)*base72 + (235374222911719/214240000000000000000000000 : ℝ)*base74 + (970204965729853/1267640000000000000000000000 : ℝ)*base76 + (175267688170502269/271579193600000000000000000000 : ℝ)*base78 + (461/6250000000000000 : ℝ)*base86 + (461/6250000000000000 : ℝ)*base88 + (461/6250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12231/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12231/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (42198342027553046055555023737/3126656801840000000000000000000000 : ℝ) := by norm_num
    linear_combination (932049/100000000000 : ℝ)*(base15) + (182701768919/1000000000000 : ℝ)*(base40) + (3204313547579/1000000000000 : ℝ)*(major_s6_0) + (3204313547579/1000000000000 : ℝ)*(major_s6_1) + (3204313547579/1000000000000 : ℝ)*(major_s6_2) + (7428177/125000000000 : ℝ)*(sp_s6_0) + (25561701/500000000000 : ℝ)*(sp_s6_1) + (2647401/100000000000 : ℝ)*(sp_s6_2) + (55248669/1000000000000 : ℝ)*(sp_s6_9) + (108010551/1000000000000 : ℝ)*(sp_s6_20) + (1073975813777/250000000000 : ℝ)*(sp_s6_21) + (536987779579/125000000000 : ℝ)*(sp_s6_22) + (2147940478923/500000000000 : ℝ)*(sp_s6_23) + (1056275952653/500000000000 : ℝ)*(sp_s6_27) + (2112659915857/1000000000000 : ℝ)*(f.failure) + (1073990670131/250000000000 : ℝ)*(f.sum) + (35472559135625426543/198308042400000000000000000000000 : ℝ)*base63 + (835041400308969/3085450000000000000000000000 : ℝ)*base65 + (108961822130039/642720000000000000000000000 : ℝ)*base67 + (1271539860077139/3085450000000000000000000000 : ℝ)*base69 + (965718265476314443/5837671400000000000000000000000 : ℝ)*base70 + (7662559176231/23650000000000000000000000 : ℝ)*base73 + (146040176602129/642720000000000000000000000 : ℝ)*base74 + (61392375178679/94600000000000000000000000 : ℝ)*base76 + (621285117657861467/1520032800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (4637/12500000000000000 : ℝ)*base86 + (4637/12500000000000000 : ℝ)*base88 + (4637/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((31691/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31691/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4017/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4017/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3147/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3147/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64/125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64/125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12231/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12231/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304063_s6 p hpa hpb X hX hprev5

#print axioms solution
