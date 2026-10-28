-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304062_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:48:30.215706+00:00
-- url     : https://prove2.me/submissions/b1df01ba-1ce2-446a-ad74-f3b56c5dfc28

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
theorem collision_support_c304062_s2_s2_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-215426933/2000000000 : ℝ)*x 0 + (78213659/156250000 : ℝ)*x 1 + (-3152665833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215426933/2000000000 : ℝ)^133 ≤ (1063389761793/20000000000000 : ℝ)^101 := by
    have hnat : (215426933 : ℕ)^133*20000000000000^101 ≤ 1063389761793^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215426933 2000000000 1063389761793 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78213659/156250000 : ℝ)^133 ≤ (40201550204161/100000000000000 : ℝ)^101 := by
    have hnat : (78213659 : ℕ)^133*100000000000000^101 ≤ 40201550204161^101*156250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78213659 156250000 40201550204161 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3152665833/5000000000 : ℝ)^133 ≤ (6810187621741/12500000000000 : ℝ)^101 := by
    have hnat : (3152665833 : ℕ)^133*12500000000000^101 ≤ 6810187621741^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3152665833 5000000000 6810187621741 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215426933/2000000000 : ℝ), (78213659/156250000 : ℝ), (-3152665833/5000000000 : ℝ)] ![(1063389761793/20000000000000 : ℝ), (40201550204161/100000000000000 : ℝ), (6810187621741/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215426933/2000000000 : ℝ)|^133 ≤ (1063389761793/20000000000000 : ℝ)^101
        have hw : |(-215426933/2000000000 : ℝ)|=(215426933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78213659/156250000 : ℝ)|^133 ≤ (40201550204161/100000000000000 : ℝ)^101
        have hw : |(78213659/156250000 : ℝ)|=(78213659/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3152665833/5000000000 : ℝ)|^133 ≤ (6810187621741/12500000000000 : ℝ)^101
        have hw : |(-3152665833/5000000000 : ℝ)|=(3152665833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2508056883/5000000000 : ℝ)*x 0 + (-134044811/1250000000 : ℝ)*x 1 + (-6298350499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2508056883/5000000000 : ℝ)^133 ≤ (40311992982869/100000000000000 : ℝ)^101 := by
    have hnat : (2508056883 : ℕ)^133*100000000000000^101 ≤ 40311992982869^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508056883 5000000000 40311992982869 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134044811/1250000000 : ℝ)^133 ≤ (660740602167/12500000000000 : ℝ)^101 := by
    have hnat : (134044811 : ℕ)^133*12500000000000^101 ≤ 660740602167^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134044811 1250000000 660740602167 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6298350499/10000000000 : ℝ)^133 ≤ (6800260273969/12500000000000 : ℝ)^101 := by
    have hnat : (6298350499 : ℕ)^133*12500000000000^101 ≤ 6800260273969^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6298350499 10000000000 6800260273969 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2508056883/5000000000 : ℝ), (-134044811/1250000000 : ℝ), (-6298350499/10000000000 : ℝ)] ![(40311992982869/100000000000000 : ℝ), (660740602167/12500000000000 : ℝ), (6800260273969/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2508056883/5000000000 : ℝ)|^133 ≤ (40311992982869/100000000000000 : ℝ)^101
        have hw : |(2508056883/5000000000 : ℝ)|=(2508056883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134044811/1250000000 : ℝ)|^133 ≤ (660740602167/12500000000000 : ℝ)^101
        have hw : |(-134044811/1250000000 : ℝ)|=(134044811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6298350499/10000000000 : ℝ)|^133 ≤ (6800260273969/12500000000000 : ℝ)^101
        have hw : |(-6298350499/10000000000 : ℝ)|=(6298350499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1456509971/10000000000 : ℝ)*x 0 + (2145519967/10000000000 : ℝ)*x 1 + (-2088529913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1456509971/10000000000 : ℝ)^133 ≤ (7910877472079/100000000000000 : ℝ)^101 := by
    have hnat : (1456509971 : ℕ)^133*100000000000000^101 ≤ 7910877472079^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456509971 10000000000 7910877472079 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145519967/10000000000 : ℝ)^133 ≤ (3293676227903/25000000000000 : ℝ)^101 := by
    have hnat : (2145519967 : ℕ)^133*25000000000000^101 ≤ 3293676227903^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145519967 10000000000 3293676227903 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088529913/2500000000 : ℝ)^133 ≤ (7891441759671/10000000000000 : ℝ)^101 := by
    have hnat : (2088529913 : ℕ)^133*10000000000000^101 ≤ 7891441759671^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088529913 2500000000 7891441759671 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1456509971/10000000000 : ℝ), (2145519967/10000000000 : ℝ), (-2088529913/2500000000 : ℝ)] ![(7910877472079/100000000000000 : ℝ), (3293676227903/25000000000000 : ℝ), (7891441759671/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1456509971/10000000000 : ℝ)|^133 ≤ (7910877472079/100000000000000 : ℝ)^101
        have hw : |(-1456509971/10000000000 : ℝ)|=(1456509971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2145519967/10000000000 : ℝ)|^133 ≤ (3293676227903/25000000000000 : ℝ)^101
        have hw : |(2145519967/10000000000 : ℝ)|=(2145519967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088529913/2500000000 : ℝ)|^133 ≤ (7891441759671/10000000000000 : ℝ)^101
        have hw : |(-2088529913/2500000000 : ℝ)|=(2088529913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2472446299/10000000000 : ℝ)*x 0 + (-538723751/5000000000 : ℝ)*x 1 + (-417250119/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2472446299/10000000000 : ℝ)^133 ≤ (1984998781867/12500000000000 : ℝ)^101 := by
    have hnat : (2472446299 : ℕ)^133*12500000000000^101 ≤ 1984998781867^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2472446299 10000000000 1984998781867 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538723751/5000000000 : ℝ)^133 ≤ (664872798371/12500000000000 : ℝ)^101 := by
    have hnat : (538723751 : ℕ)^133*12500000000000^101 ≤ 664872798371^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538723751 5000000000 664872798371 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417250119/500000000 : ℝ)^133 ≤ (78801027341153/100000000000000 : ℝ)^101 := by
    have hnat : (417250119 : ℕ)^133*100000000000000^101 ≤ 78801027341153^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417250119 500000000 78801027341153 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2472446299/10000000000 : ℝ), (-538723751/5000000000 : ℝ), (-417250119/500000000 : ℝ)] ![(1984998781867/12500000000000 : ℝ), (664872798371/12500000000000 : ℝ), (78801027341153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2472446299/10000000000 : ℝ)|^133 ≤ (1984998781867/12500000000000 : ℝ)^101
        have hw : |(2472446299/10000000000 : ℝ)|=(2472446299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-538723751/5000000000 : ℝ)|^133 ≤ (664872798371/12500000000000 : ℝ)^101
        have hw : |(-538723751/5000000000 : ℝ)|=(538723751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-417250119/500000000 : ℝ)|^133 ≤ (78801027341153/100000000000000 : ℝ)^101
        have hw : |(-417250119/500000000 : ℝ)|=(417250119/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (738336551/2500000000 : ℝ)*x 0 + (7445992991/10000000000 : ℝ)*x 1 + (2013118493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (738336551/2500000000 : ℝ)^133 ≤ (20067495159749/100000000000000 : ℝ)^101 := by
    have hnat : (738336551 : ℕ)^133*100000000000000^101 ≤ 20067495159749^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738336551 2500000000 20067495159749 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7445992991/10000000000 : ℝ)^133 ≤ (67817792965403/100000000000000 : ℝ)^101 := by
    have hnat : (7445992991 : ℕ)^133*100000000000000^101 ≤ 67817792965403^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7445992991 10000000000 67817792965403 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013118493/10000000000 : ℝ)^133 ≤ (3028677964803/25000000000000 : ℝ)^101 := by
    have hnat : (2013118493 : ℕ)^133*25000000000000^101 ≤ 3028677964803^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013118493 10000000000 3028677964803 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(738336551/2500000000 : ℝ), (7445992991/10000000000 : ℝ), (2013118493/10000000000 : ℝ)] ![(20067495159749/100000000000000 : ℝ), (67817792965403/100000000000000 : ℝ), (3028677964803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(738336551/2500000000 : ℝ)|^133 ≤ (20067495159749/100000000000000 : ℝ)^101
        have hw : |(738336551/2500000000 : ℝ)|=(738336551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7445992991/10000000000 : ℝ)|^133 ≤ (67817792965403/100000000000000 : ℝ)^101
        have hw : |(7445992991/10000000000 : ℝ)|=(7445992991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2013118493/10000000000 : ℝ)|^133 ≤ (3028677964803/25000000000000 : ℝ)^101
        have hw : |(2013118493/10000000000 : ℝ)|=(2013118493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (371187381/1000000000 : ℝ)*x 0 + (983087699/1250000000 : ℝ)*x 1 + (160591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (371187381/1000000000 : ℝ)^133 ≤ (13558033351797/50000000000000 : ℝ)^101 := by
    have hnat : (371187381 : ℕ)^133*50000000000000^101 ≤ 13558033351797^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371187381 1000000000 13558033351797 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983087699/1250000000 : ℝ)^133 ≤ (72883812186369/100000000000000 : ℝ)^101 := by
    have hnat : (983087699 : ℕ)^133*100000000000000^101 ≤ 72883812186369^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983087699 1250000000 72883812186369 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160591/5000000000 : ℝ)^133 ≤ (121100969/100000000000000 : ℝ)^101 := by
    have hnat : (160591 : ℕ)^133*100000000000000^101 ≤ 121100969^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160591 5000000000 121100969 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(371187381/1000000000 : ℝ), (983087699/1250000000 : ℝ), (160591/5000000000 : ℝ)] ![(13558033351797/50000000000000 : ℝ), (72883812186369/100000000000000 : ℝ), (121100969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(371187381/1000000000 : ℝ)|^133 ≤ (13558033351797/50000000000000 : ℝ)^101
        have hw : |(371187381/1000000000 : ℝ)|=(371187381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(983087699/1250000000 : ℝ)|^133 ≤ (72883812186369/100000000000000 : ℝ)^101
        have hw : |(983087699/1250000000 : ℝ)|=(983087699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160591/5000000000 : ℝ)|^133 ≤ (121100969/100000000000000 : ℝ)^101
        have hw : |(160591/5000000000 : ℝ)|=(160591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1159493109/10000000000 : ℝ)*x 0 + (2366798247/10000000000 : ℝ)*x 1 + (-1674590743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1159493109/10000000000 : ℝ)^133 ≤ (1171733043681/20000000000000 : ℝ)^101 := by
    have hnat : (1159493109 : ℕ)^133*20000000000000^101 ≤ 1171733043681^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159493109 10000000000 1171733043681 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2366798247/10000000000 : ℝ)^133 ≤ (14992556386519/100000000000000 : ℝ)^101 := by
    have hnat : (2366798247 : ℕ)^133*100000000000000^101 ≤ 14992556386519^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366798247 10000000000 14992556386519 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1674590743/2000000000 : ℝ)^133 ≤ (79148778384103/100000000000000 : ℝ)^101 := by
    have hnat : (1674590743 : ℕ)^133*100000000000000^101 ≤ 79148778384103^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674590743 2000000000 79148778384103 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1159493109/10000000000 : ℝ), (2366798247/10000000000 : ℝ), (-1674590743/2000000000 : ℝ)] ![(1171733043681/20000000000000 : ℝ), (14992556386519/100000000000000 : ℝ), (79148778384103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1159493109/10000000000 : ℝ)|^133 ≤ (1171733043681/20000000000000 : ℝ)^101
        have hw : |(-1159493109/10000000000 : ℝ)|=(1159493109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2366798247/10000000000 : ℝ)|^133 ≤ (14992556386519/100000000000000 : ℝ)^101
        have hw : |(2366798247/10000000000 : ℝ)|=(2366798247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1674590743/2000000000 : ℝ)|^133 ≤ (79148778384103/100000000000000 : ℝ)^101
        have hw : |(-1674590743/2000000000 : ℝ)|=(1674590743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2060549369/10000000000 : ℝ)*x 0 + (-767228641/5000000000 : ℝ)*x 1 + (-2090952543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060549369/10000000000 : ℝ)^133 ≤ (6245987569139/50000000000000 : ℝ)^101 := by
    have hnat : (2060549369 : ℕ)^133*50000000000000^101 ≤ 6245987569139^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060549369 10000000000 6245987569139 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (767228641/5000000000 : ℝ)^133 ≤ (211826115013/2500000000000 : ℝ)^101 := by
    have hnat : (767228641 : ℕ)^133*2500000000000^101 ≤ 211826115013^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767228641 5000000000 211826115013 2500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2090952543/2500000000 : ℝ)^133 ≤ (19758745062029/25000000000000 : ℝ)^101 := by
    have hnat : (2090952543 : ℕ)^133*25000000000000^101 ≤ 19758745062029^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090952543 2500000000 19758745062029 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2060549369/10000000000 : ℝ), (-767228641/5000000000 : ℝ), (-2090952543/2500000000 : ℝ)] ![(6245987569139/50000000000000 : ℝ), (211826115013/2500000000000 : ℝ), (19758745062029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2060549369/10000000000 : ℝ)|^133 ≤ (6245987569139/50000000000000 : ℝ)^101
        have hw : |(2060549369/10000000000 : ℝ)|=(2060549369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-767228641/5000000000 : ℝ)|^133 ≤ (211826115013/2500000000000 : ℝ)^101
        have hw : |(-767228641/5000000000 : ℝ)|=(767228641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2090952543/2500000000 : ℝ)|^133 ≤ (19758745062029/25000000000000 : ℝ)^101
        have hw : |(-2090952543/2500000000 : ℝ)|=(2090952543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1458350069/2000000000 : ℝ)*x 0 + (195342097/625000000 : ℝ)*x 1 + (204956683/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1458350069/2000000000 : ℝ)^133 ≤ (16493490131561/25000000000000 : ℝ)^101 := by
    have hnat : (1458350069 : ℕ)^133*25000000000000^101 ≤ 16493490131561^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458350069 2000000000 16493490131561 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195342097/625000000 : ℝ)^133 ≤ (10810833139917/50000000000000 : ℝ)^101 := by
    have hnat : (195342097 : ℕ)^133*50000000000000^101 ≤ 10810833139917^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195342097 625000000 10810833139917 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204956683/1000000000 : ℝ)^133 ≤ (12404373180147/100000000000000 : ℝ)^101 := by
    have hnat : (204956683 : ℕ)^133*100000000000000^101 ≤ 12404373180147^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204956683 1000000000 12404373180147 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1458350069/2000000000 : ℝ), (195342097/625000000 : ℝ), (204956683/1000000000 : ℝ)] ![(16493490131561/25000000000000 : ℝ), (10810833139917/50000000000000 : ℝ), (12404373180147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1458350069/2000000000 : ℝ)|^133 ≤ (16493490131561/25000000000000 : ℝ)^101
        have hw : |(1458350069/2000000000 : ℝ)|=(1458350069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195342097/625000000 : ℝ)|^133 ≤ (10810833139917/50000000000000 : ℝ)^101
        have hw : |(195342097/625000000 : ℝ)|=(195342097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204956683/1000000000 : ℝ)|^133 ≤ (12404373180147/100000000000000 : ℝ)^101
        have hw : |(204956683/1000000000 : ℝ)|=(204956683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4003114679/5000000000 : ℝ)*x 0 + (882599981/2500000000 : ℝ)*x 1 + (403461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4003114679/5000000000 : ℝ)^133 ≤ (74615828703343/100000000000000 : ℝ)^101 := by
    have hnat : (4003114679 : ℕ)^133*100000000000000^101 ≤ 74615828703343^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003114679 5000000000 74615828703343 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882599981/2500000000 : ℝ)^133 ≤ (5076801551919/20000000000000 : ℝ)^101 := by
    have hnat : (882599981 : ℕ)^133*20000000000000^101 ≤ 5076801551919^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882599981 2500000000 5076801551919 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403461/10000000000 : ℝ)^133 ≤ (81761769/50000000000000 : ℝ)^101 := by
    have hnat : (403461 : ℕ)^133*50000000000000^101 ≤ 81761769^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403461 10000000000 81761769 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4003114679/5000000000 : ℝ), (882599981/2500000000 : ℝ), (403461/10000000000 : ℝ)] ![(74615828703343/100000000000000 : ℝ), (5076801551919/20000000000000 : ℝ), (81761769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4003114679/5000000000 : ℝ)|^133 ≤ (74615828703343/100000000000000 : ℝ)^101
        have hw : |(4003114679/5000000000 : ℝ)|=(4003114679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(882599981/2500000000 : ℝ)|^133 ≤ (5076801551919/20000000000000 : ℝ)^101
        have hw : |(882599981/2500000000 : ℝ)|=(882599981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403461/10000000000 : ℝ)|^133 ≤ (81761769/50000000000000 : ℝ)^101
        have hw : |(403461/10000000000 : ℝ)|=(403461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-389136293/10000000000 : ℝ)*x 0 + (1771792979/2500000000 : ℝ)*x 1 + (-4511731857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389136293/10000000000 : ℝ)^133 ≤ (278247514383/20000000000000 : ℝ)^101 := by
    have hnat : (389136293 : ℕ)^133*20000000000000^101 ≤ 278247514383^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389136293 10000000000 278247514383 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1771792979/2500000000 : ℝ)^133 ≤ (31773720487111/50000000000000 : ℝ)^101 := by
    have hnat : (1771792979 : ℕ)^133*50000000000000^101 ≤ 31773720487111^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771792979 2500000000 31773720487111 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511731857/10000000000 : ℝ)^133 ≤ (35061321440833/100000000000000 : ℝ)^101 := by
    have hnat : (4511731857 : ℕ)^133*100000000000000^101 ≤ 35061321440833^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511731857 10000000000 35061321440833 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-389136293/10000000000 : ℝ), (1771792979/2500000000 : ℝ), (-4511731857/10000000000 : ℝ)] ![(278247514383/20000000000000 : ℝ), (31773720487111/50000000000000 : ℝ), (35061321440833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-389136293/10000000000 : ℝ)|^133 ≤ (278247514383/20000000000000 : ℝ)^101
        have hw : |(-389136293/10000000000 : ℝ)|=(389136293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1771792979/2500000000 : ℝ)|^133 ≤ (31773720487111/50000000000000 : ℝ)^101
        have hw : |(1771792979/2500000000 : ℝ)|=(1771792979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4511731857/10000000000 : ℝ)|^133 ≤ (35061321440833/100000000000000 : ℝ)^101
        have hw : |(-4511731857/10000000000 : ℝ)|=(4511731857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7204648873/10000000000 : ℝ)*x 0 + (-28448441/625000000 : ℝ)*x 1 + (-434365987/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7204648873/10000000000 : ℝ)^133 ≤ (162345426531/250000000000 : ℝ)^101 := by
    have hnat : (7204648873 : ℕ)^133*250000000000^101 ≤ 162345426531^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7204648873 10000000000 162345426531 250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28448441/625000000 : ℝ)^133 ≤ (427549973797/25000000000000 : ℝ)^101 := by
    have hnat : (28448441 : ℕ)^133*25000000000000^101 ≤ 427549973797^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28448441 625000000 427549973797 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434365987/1000000000 : ℝ)^133 ≤ (33351629484343/100000000000000 : ℝ)^101 := by
    have hnat : (434365987 : ℕ)^133*100000000000000^101 ≤ 33351629484343^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434365987 1000000000 33351629484343 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7204648873/10000000000 : ℝ), (-28448441/625000000 : ℝ), (-434365987/1000000000 : ℝ)] ![(162345426531/250000000000 : ℝ), (427549973797/25000000000000 : ℝ), (33351629484343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7204648873/10000000000 : ℝ)|^133 ≤ (162345426531/250000000000 : ℝ)^101
        have hw : |(7204648873/10000000000 : ℝ)|=(7204648873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28448441/625000000 : ℝ)|^133 ≤ (427549973797/25000000000000 : ℝ)^101
        have hw : |(-28448441/625000000 : ℝ)|=(28448441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434365987/1000000000 : ℝ)|^133 ≤ (33351629484343/100000000000000 : ℝ)^101
        have hw : |(-434365987/1000000000 : ℝ)|=(434365987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1361107839/5000000000 : ℝ)*x 0 + (3769582979/5000000000 : ℝ)*x 1 + (425693291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1361107839/5000000000 : ℝ)^133 ≤ (563297867223/3125000000000 : ℝ)^101 := by
    have hnat : (1361107839 : ℕ)^133*3125000000000^101 ≤ 563297867223^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361107839 5000000000 563297867223 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3769582979/5000000000 : ℝ)^133 ≤ (4308592851239/6250000000000 : ℝ)^101 := by
    have hnat : (3769582979 : ℕ)^133*6250000000000^101 ≤ 4308592851239^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3769582979 5000000000 4308592851239 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425693291/2000000000 : ℝ)^133 ≤ (6518491308417/50000000000000 : ℝ)^101 := by
    have hnat : (425693291 : ℕ)^133*50000000000000^101 ≤ 6518491308417^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425693291 2000000000 6518491308417 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1361107839/5000000000 : ℝ), (3769582979/5000000000 : ℝ), (425693291/2000000000 : ℝ)] ![(563297867223/3125000000000 : ℝ), (4308592851239/6250000000000 : ℝ), (6518491308417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1361107839/5000000000 : ℝ)|^133 ≤ (563297867223/3125000000000 : ℝ)^101
        have hw : |(1361107839/5000000000 : ℝ)|=(1361107839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3769582979/5000000000 : ℝ)|^133 ≤ (4308592851239/6250000000000 : ℝ)^101
        have hw : |(3769582979/5000000000 : ℝ)|=(3769582979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425693291/2000000000 : ℝ)|^133 ≤ (6518491308417/50000000000000 : ℝ)^101
        have hw : |(425693291/2000000000 : ℝ)|=(425693291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s2_s2_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2092833547/2500000000 : ℝ)*x 0 + (3030458461/10000000000 : ℝ)*x 1 + (-14268713/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092833547/2500000000 : ℝ)^133 ≤ (15825723861107/20000000000000 : ℝ)^101 := by
    have hnat : (2092833547 : ℕ)^133*20000000000000^101 ≤ 15825723861107^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092833547 2500000000 15825723861107 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3030458461/10000000000 : ℝ)^133 ≤ (10380152953843/50000000000000 : ℝ)^101 := by
    have hnat : (3030458461 : ℕ)^133*50000000000000^101 ≤ 10380152953843^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3030458461 10000000000 10380152953843 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14268713/2500000000 : ℝ)^133 ≤ (111074769789/100000000000000 : ℝ)^101 := by
    have hnat : (14268713 : ℕ)^133*100000000000000^101 ≤ 111074769789^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14268713 2500000000 111074769789 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2092833547/2500000000 : ℝ), (3030458461/10000000000 : ℝ), (-14268713/2500000000 : ℝ)] ![(15825723861107/20000000000000 : ℝ), (10380152953843/50000000000000 : ℝ), (111074769789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2092833547/2500000000 : ℝ)|^133 ≤ (15825723861107/20000000000000 : ℝ)^101
        have hw : |(2092833547/2500000000 : ℝ)|=(2092833547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3030458461/10000000000 : ℝ)|^133 ≤ (10380152953843/50000000000000 : ℝ)^101
        have hw : |(3030458461/10000000000 : ℝ)|=(3030458461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14268713/2500000000 : ℝ)|^133 ≤ (111074769789/100000000000000 : ℝ)^101
        have hw : |(-14268713/2500000000 : ℝ)|=(14268713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304062_s2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((92539/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92539/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46001/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46001/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38341/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38341/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((85451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4263/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4263/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6873/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6873/10000 : ℝ)*X 1 2) := by
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
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (92539/100000 : ℝ) ^ (33/8 : ℝ) ≤ (18156403146904023743/25000000000000000000 : ℝ) := by
    have hpowers : (92539/100000 : ℝ)^33 ≤ (18156403146904023743/25000000000000000000 : ℝ)^8 := by
      have hnat : (92539 : ℕ)^33*25000000000000000000^8 ≤ 18156403146904023743^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92539 100000 18156403146904023743 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92539/100000 : ℝ)) (X := (18156403146904023743/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (43156403146904023743/25000000000000000000 : ℝ) ≤ (2853777208004839/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (43156403146904023743/25000000000000000000 : ℝ)^8 ≤ (2853777208004839/2500000000000000 : ℝ)^33 := by
      have hnat : (43156403146904023743 : ℕ)^8*2500000000000000^33 ≤ 2853777208004839^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43156403146904023743 25000000000000000000 2853777208004839 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2853777208004839/2500000000000000 : ℝ)) (X := (43156403146904023743/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (30656403146904023743/12500000000000000000 : ℝ) ≤ (6214714766494687/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (30656403146904023743/12500000000000000000 : ℝ)^8 ≤ (6214714766494687/5000000000000000 : ℝ)^33 := by
      have hnat : (30656403146904023743 : ℕ)^8*5000000000000000^33 ≤ 6214714766494687^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30656403146904023743 12500000000000000000 6214714766494687 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6214714766494687/5000000000000000 : ℝ)) (X := (30656403146904023743/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(353777208004839/2313475000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(507160350485009/4626950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (92539/100000 : ℝ)) (alpha := (353777208004839/2313475000000000 : ℝ)) (beta := (507160350485009/4626950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (92539/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(353777208004839/2313475000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(507160350485009/4626950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (46001/50000 : ℝ) ^ (33/8 : ℝ) ≤ (7090285651323879677/10000000000000000000 : ℝ) := by
    have hpowers : (46001/50000 : ℝ)^33 ≤ (7090285651323879677/10000000000000000000 : ℝ)^8 := by
      have hnat : (46001 : ℕ)^33*10000000000000000000^8 ≤ 7090285651323879677^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46001 50000 7090285651323879677 10000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (46001/50000 : ℝ)) (X := (7090285651323879677/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (17090285651323879677/10000000000000000000 : ℝ) ≤ (11387386937060767/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (17090285651323879677/10000000000000000000 : ℝ)^8 ≤ (11387386937060767/10000000000000000 : ℝ)^33 := by
      have hnat : (17090285651323879677 : ℕ)^8*10000000000000000^33 ≤ 11387386937060767^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17090285651323879677 10000000000000000000 11387386937060767 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11387386937060767/10000000000000000 : ℝ)) (X := (17090285651323879677/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (12090285651323879677/5000000000000000000 : ℝ) ≤ (1548358785634439/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (12090285651323879677/5000000000000000000 : ℝ)^8 ≤ (1548358785634439/1250000000000000 : ℝ)^33 := by
      have hnat : (12090285651323879677 : ℕ)^8*1250000000000000^33 ≤ 1548358785634439^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12090285651323879677 5000000000000000000 1548358785634439 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1548358785634439/1250000000000000 : ℝ)) (X := (12090285651323879677/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1387386937060767/9200200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(199896669602949/1840040000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (46001/50000 : ℝ)) (alpha := (1387386937060767/9200200000000000 : ℝ)) (beta := (199896669602949/1840040000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (46001/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1387386937060767/9200200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(199896669602949/1840040000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (38341/50000 : ℝ) ^ (33/8 : ℝ) ≤ (33447249127458817907/100000000000000000000 : ℝ) := by
    have hpowers : (38341/50000 : ℝ)^33 ≤ (33447249127458817907/100000000000000000000 : ℝ)^8 := by
      have hnat : (38341 : ℕ)^33*100000000000000000000^8 ≤ 33447249127458817907^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38341 50000 33447249127458817907 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38341/50000 : ℝ)) (X := (33447249127458817907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (133447249127458817907/100000000000000000000 : ℝ) ≤ (41892678205831/39062500000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (133447249127458817907/100000000000000000000 : ℝ)^8 ≤ (41892678205831/39062500000000 : ℝ)^33 := by
      have hnat : (133447249127458817907 : ℕ)^8*39062500000000^33 ≤ 41892678205831^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133447249127458817907 100000000000000000000 41892678205831 39062500000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (41892678205831/39062500000000 : ℝ)) (X := (133447249127458817907/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (83447249127458817907/50000000000000000000 : ℝ) ≤ (11322057032849967/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (83447249127458817907/50000000000000000000 : ℝ)^8 ≤ (11322057032849967/10000000000000000 : ℝ)^33 := by
      have hnat : (83447249127458817907 : ℕ)^8*10000000000000000^33 ≤ 11322057032849967^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83447249127458817907 50000000000000000000 11322057032849967 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11322057032849967/10000000000000000 : ℝ)) (X := (83447249127458817907/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(2830178205831/29953906250000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(597531412157231/7668200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (38341/50000 : ℝ)) (alpha := (2830178205831/29953906250000 : ℝ)) (beta := (597531412157231/7668200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (38341/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(2830178205831/29953906250000 : ℝ)*((1 : ℝ)*pair X 2 0)+(597531412157231/7668200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-215426933/2000000000 : ℝ)*X 0 0+(78213659/156250000 : ℝ)*X 0 1+(-3152665833/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((2508056883/5000000000 : ℝ)*X 1 0+(-134044811/1250000000 : ℝ)*X 1 1+(-6298350499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1456509971/10000000000 : ℝ)*X 0 0+(2145519967/10000000000 : ℝ)*X 0 1+(-2088529913/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2472446299/10000000000 : ℝ)*X 1 0+(-538723751/5000000000 : ℝ)*X 1 1+(-417250119/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((738336551/2500000000 : ℝ)*X 2 0+(7445992991/10000000000 : ℝ)*X 2 1+(2013118493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((371187381/1000000000 : ℝ)*X 0 0+(983087699/1250000000 : ℝ)*X 0 1+(160591/5000000000 : ℝ)*X 0 2+(371187381/1000000000 : ℝ)*X 1 0+(983087699/1250000000 : ℝ)*X 1 1+(160591/5000000000 : ℝ)*X 1 2+(371187381/1000000000 : ℝ)*X 2 0+(983087699/1250000000 : ℝ)*X 2 1+(160591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1159493109/10000000000 : ℝ)*X 0 0+(2366798247/10000000000 : ℝ)*X 0 1+(-1674590743/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2060549369/10000000000 : ℝ)*X 1 0+(-767228641/5000000000 : ℝ)*X 1 1+(-2090952543/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1458350069/2000000000 : ℝ)*X 2 0+(195342097/625000000 : ℝ)*X 2 1+(204956683/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((4003114679/5000000000 : ℝ)*X 0 0+(882599981/2500000000 : ℝ)*X 0 1+(403461/10000000000 : ℝ)*X 0 2+(4003114679/5000000000 : ℝ)*X 1 0+(882599981/2500000000 : ℝ)*X 1 1+(403461/10000000000 : ℝ)*X 1 2+(4003114679/5000000000 : ℝ)*X 2 0+(882599981/2500000000 : ℝ)*X 2 1+(403461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-389136293/10000000000 : ℝ)*X 0 0+(1771792979/2500000000 : ℝ)*X 0 1+(-4511731857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((7204648873/10000000000 : ℝ)*X 1 0+(-28448441/625000000 : ℝ)*X 1 1+(-434365987/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1361107839/5000000000 : ℝ)*X 2 0+(3769582979/5000000000 : ℝ)*X 2 1+(425693291/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2092833547/2500000000 : ℝ)*X 0 0+(3030458461/10000000000 : ℝ)*X 0 1+(-14268713/2500000000 : ℝ)*X 0 2+(2092833547/2500000000 : ℝ)*X 1 0+(3030458461/10000000000 : ℝ)*X 1 1+(-14268713/2500000000 : ℝ)*X 1 2+(2092833547/2500000000 : ℝ)*X 2 0+(3030458461/10000000000 : ℝ)*X 2 1+(-14268713/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((85451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (71534805797870725663542924177/16321328679179900000000000000000000 : ℝ) := by norm_num
    linear_combination (16829895907/500000000000 : ℝ)*(base5) + (868704554337/1000000000000 : ℝ)*(base7) + (92433/500000000000 : ℝ)*(base59) + (496837115403/250000000000 : ℝ)*(major_s2_0) + (496837115403/250000000000 : ℝ)*(major_s2_1) + (496837115403/250000000000 : ℝ)*(major_s2_2) + (1491419/1000000000000 : ℝ)*(sp_s2_0) + (2963263/1000000000000 : ℝ)*(sp_s2_1) + (424106108347/200000000000 : ℝ)*(sp_s2_7) + (530123465987/250000000000 : ℝ)*(sp_s2_8) + (430838122593/200000000000 : ℝ)*(sp_s2_9) + (429067666257/200000000000 : ℝ)*(sp_s2_13) + (35205943/1000000000000 : ℝ)*(sp_s2_15) + (1212003/1000000000000 : ℝ)*(sp_s2_23) + (1310293568761/1000000000000 : ℝ)*(f.failure) + (1060266016577/500000000000 : ℝ)*(f.sum) + (11692129202853273399/88186217050000000000000000000000 : ℝ)*base63 + (393098996610687/479262500000000000000000000 : ℝ)*base65 + (44627314421149/460010000000000000000000000 : ℝ)*base66 + (642318490283073/1917050000000000000000000000 : ℝ)*base69 + (125435635644893171073/177401889950000000000000000000000 : ℝ)*base71 + (217022897516407/4626950000000000000000000000 : ℝ)*base72 + (305754544255381/2300050000000000000000000000 : ℝ)*base75 + (146497423873819/4626950000000000000000000000 : ℝ)*base76 + (15817271717474193927/212844326950000000000000000000000 : ℝ)*base78 + (10201/12500000000000000 : ℝ)*base86 + (10201/12500000000000000 : ℝ)*base88 + (10201/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4263/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4263/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18879096066313337344278051/1774018899500000000000000000000 : ℝ) := by norm_num
    linear_combination (139979/1000000000000 : ℝ)*(base5) + (43537127463/50000000000 : ℝ)*(base7) + (849243/1000000000000 : ℝ)*(base18) + (50897/125000000000 : ℝ)*(base40) + (178119411/15625000000 : ℝ)*(base60) + (24684847177/12500000000 : ℝ)*(major_s2_0) + (24684847177/12500000000 : ℝ)*(major_s2_1) + (24684847177/12500000000 : ℝ)*(major_s2_2) + (883289/125000000000 : ℝ)*(sp_s2_0) + (107402277/1000000000000 : ℝ)*(sp_s2_8) + (2102407058827/1000000000000 : ℝ)*(sp_s2_14) + (2102305873619/1000000000000 : ℝ)*(sp_s2_15) + (1051207132559/500000000000 : ℝ)*(sp_s2_16) + (2172754497313/1000000000000 : ℝ)*(sp_s2_20) + (40687877751/31250000000 : ℝ)*(f.failure) + (2102414125139/1000000000000 : ℝ)*(f.sum) + (6855129808591415393/17637243410000000000000000000000 : ℝ)*base63 + (43256680243893/76682000000000000000000000 : ℝ)*base64 + (4938483678477/14375312500000000000000000 : ℝ)*base67 + (548871921111/4792625000000000000000000 : ℝ)*base69 + (422551272192641927/8870094497500000000000000000000 : ℝ)*base71 + (2117634563047/925390000000000000000000000 : ℝ)*base72 + (5174014256429/14375312500000000000000000 : ℝ)*base74 + (22153356499119/231347500000000000000000000 : ℝ)*base76 + (20073888869537277159/42568865390000000000000000000000 : ℝ)*base78 + (41/390625000000000 : ℝ)*base86 + (41/390625000000000 : ℝ)*base88 + (41/390625000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6873/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6873/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12318752355322384669323/1917050000000000000000000000 : ℝ) := by norm_num
    linear_combination (314839703671/500000000000 : ℝ)*(base7) + (436691/1000000000000 : ℝ)*(base34) + (12169663633/500000000000 : ℝ)*(base39) + (846640223/62500000000 : ℝ)*(base43) + (11042910993/250000000000 : ℝ)*(base59) + (446952551183/250000000000 : ℝ)*(major_s2_0) + (354852879571/200000000000 : ℝ)*(major_s2_1) + (1787810641423/1000000000000 : ℝ)*(major_s2_2) + (17421683/1000000000000 : ℝ)*(sp_s2_0) + (221887951/1000000000000 : ℝ)*(sp_s2_9) + (248637106913/125000000000 : ℝ)*(sp_s2_21) + (1001330478623/500000000000 : ℝ)*(sp_s2_22) + (15538225201/7812500000 : ℝ)*(sp_s2_23) + (113025860483/62500000000 : ℝ)*(sp_s2_27) + (1178734797077/1000000000000 : ℝ)*(f.failure) + (1001330478623/500000000000 : ℝ)*(f.sum) + (23069340705699271473/352744868200000000000000000000000 : ℝ)*base63 + (2078775383669887/7668200000000000000000000000 : ℝ)*base64 + (352029231521043/1840040000000000000000000000 : ℝ)*base67 + (86989035760161/958525000000000000000000000 : ℝ)*base69 + (81459517168043425691/709607559800000000000000000000000 : ℝ)*base71 + (123273912362051/578368750000000000000000000 : ℝ)*base73 + (177848067422851/1840040000000000000000000000 : ℝ)*base74 + (4546749361633439/4626950000000000000000000000 : ℝ)*base76 + (156771948813718418183/851377307800000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (4657/12500000000000000 : ℝ)*base86 + (4657/12500000000000000 : ℝ)*base88 + (4657/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((92539/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92539/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46001/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46001/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38341/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38341/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((85451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4263/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4263/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6873/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6873/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304062_s2 p hpa hpb X hX hprev1

#print axioms solution
