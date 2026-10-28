-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301076_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:42:08.202865+00:00
-- url     : https://prove2.me/submissions/f58f3ed7-cdb7-4fb0-825a-309b4c8e8135

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
theorem collision_support_c301076_s3_s3_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-453787657/2000000000 : ℝ)*x 0 + (-566151643/1000000000 : ℝ)*x 1 + (1229407411/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453787657/2000000000 : ℝ)^65 ≤ (13979095429029/100000000000000 : ℝ)^49 := by
    have hnat : (453787657 : ℕ)^65*100000000000000^49 ≤ 13979095429029^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453787657 2000000000 13979095429029 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566151643/1000000000 : ℝ)^65 ≤ (47017307894171/100000000000000 : ℝ)^49 := by
    have hnat : (566151643 : ℕ)^65*100000000000000^49 ≤ 47017307894171^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566151643 1000000000 47017307894171 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229407411/2500000000 : ℝ)^65 ≤ (9750899163837/25000000000000 : ℝ)^49 := by
    have hnat : (1229407411 : ℕ)^65*25000000000000^49 ≤ 9750899163837^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229407411 2500000000 9750899163837 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-453787657/2000000000 : ℝ), (-566151643/1000000000 : ℝ), (1229407411/2500000000 : ℝ)] ![(13979095429029/100000000000000 : ℝ), (47017307894171/100000000000000 : ℝ), (9750899163837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-453787657/2000000000 : ℝ)|^65 ≤ (13979095429029/100000000000000 : ℝ)^49
        have hw : |(-453787657/2000000000 : ℝ)|=(453787657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-566151643/1000000000 : ℝ)|^65 ≤ (47017307894171/100000000000000 : ℝ)^49
        have hw : |(-566151643/1000000000 : ℝ)|=(566151643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1229407411/2500000000 : ℝ)|^65 ≤ (9750899163837/25000000000000 : ℝ)^49
        have hw : |(1229407411/2500000000 : ℝ)|=(1229407411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5842411111/10000000000 : ℝ)*x 0 + (979641747/2500000000 : ℝ)*x 1 + (1603456417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5842411111/10000000000 : ℝ)^65 ≤ (24510224989819/50000000000000 : ℝ)^49 := by
    have hnat : (5842411111 : ℕ)^65*50000000000000^49 ≤ 24510224989819^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5842411111 10000000000 24510224989819 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (979641747/2500000000 : ℝ)^65 ≤ (14429154376473/50000000000000 : ℝ)^49 := by
    have hnat : (979641747 : ℕ)^65*50000000000000^49 ≤ 14429154376473^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979641747 2500000000 14429154376473 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1603456417/5000000000 : ℝ)^65 ≤ (11060620627921/50000000000000 : ℝ)^49 := by
    have hnat : (1603456417 : ℕ)^65*50000000000000^49 ≤ 11060620627921^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1603456417 5000000000 11060620627921 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5842411111/10000000000 : ℝ), (979641747/2500000000 : ℝ), (1603456417/5000000000 : ℝ)] ![(24510224989819/50000000000000 : ℝ), (14429154376473/50000000000000 : ℝ), (11060620627921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5842411111/10000000000 : ℝ)|^65 ≤ (24510224989819/50000000000000 : ℝ)^49
        have hw : |(5842411111/10000000000 : ℝ)|=(5842411111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(979641747/2500000000 : ℝ)|^65 ≤ (14429154376473/50000000000000 : ℝ)^49
        have hw : |(979641747/2500000000 : ℝ)|=(979641747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1603456417/5000000000 : ℝ)|^65 ≤ (11060620627921/50000000000000 : ℝ)^49
        have hw : |(1603456417/5000000000 : ℝ)|=(1603456417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4747387547/10000000000 : ℝ)*x 0 + (-324845813/2500000000 : ℝ)*x 1 + (1617036659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4747387547/10000000000 : ℝ)^65 ≤ (18611322777823/50000000000000 : ℝ)^49 := by
    have hnat : (4747387547 : ℕ)^65*50000000000000^49 ≤ 18611322777823^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4747387547 10000000000 18611322777823 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324845813/2500000000 : ℝ)^65 ≤ (83417153151/1250000000000 : ℝ)^49 := by
    have hnat : (324845813 : ℕ)^65*1250000000000^49 ≤ 83417153151^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324845813 2500000000 83417153151 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1617036659/2500000000 : ℝ)^65 ≤ (56103982170139/100000000000000 : ℝ)^49 := by
    have hnat : (1617036659 : ℕ)^65*100000000000000^49 ≤ 56103982170139^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617036659 2500000000 56103982170139 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4747387547/10000000000 : ℝ), (-324845813/2500000000 : ℝ), (1617036659/2500000000 : ℝ)] ![(18611322777823/50000000000000 : ℝ), (83417153151/1250000000000 : ℝ), (56103982170139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4747387547/10000000000 : ℝ)|^65 ≤ (18611322777823/50000000000000 : ℝ)^49
        have hw : |(4747387547/10000000000 : ℝ)|=(4747387547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-324845813/2500000000 : ℝ)|^65 ≤ (83417153151/1250000000000 : ℝ)^49
        have hw : |(-324845813/2500000000 : ℝ)|=(324845813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1617036659/2500000000 : ℝ)|^65 ≤ (56103982170139/100000000000000 : ℝ)^49
        have hw : |(1617036659/2500000000 : ℝ)|=(1617036659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033221267/5000000000 : ℝ)*x 0 + (-6086725221/10000000000 : ℝ)*x 1 + (230949589/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033221267/5000000000 : ℝ)^65 ≤ (2469748802781/20000000000000 : ℝ)^49 := by
    have hnat : (1033221267 : ℕ)^65*20000000000000^49 ≤ 2469748802781^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033221267 5000000000 2469748802781 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6086725221/10000000000 : ℝ)^65 ≤ (12939526413957/25000000000000 : ℝ)^49 := by
    have hnat : (6086725221 : ℕ)^65*25000000000000^49 ≤ 12939526413957^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6086725221 10000000000 12939526413957 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230949589/500000000 : ℝ)^65 ≤ (17946575158779/50000000000000 : ℝ)^49 := by
    have hnat : (230949589 : ℕ)^65*50000000000000^49 ≤ 17946575158779^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230949589 500000000 17946575158779 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033221267/5000000000 : ℝ), (-6086725221/10000000000 : ℝ), (230949589/500000000 : ℝ)] ![(2469748802781/20000000000000 : ℝ), (12939526413957/25000000000000 : ℝ), (17946575158779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033221267/5000000000 : ℝ)|^65 ≤ (2469748802781/20000000000000 : ℝ)^49
        have hw : |(-1033221267/5000000000 : ℝ)|=(1033221267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6086725221/10000000000 : ℝ)|^65 ≤ (12939526413957/25000000000000 : ℝ)^49
        have hw : |(-6086725221/10000000000 : ℝ)|=(6086725221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(230949589/500000000 : ℝ)|^65 ≤ (17946575158779/50000000000000 : ℝ)^49
        have hw : |(230949589/500000000 : ℝ)|=(230949589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2963857403/5000000000 : ℝ)*x 0 + (237967217/625000000 : ℝ)*x 1 + (3220948367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2963857403/5000000000 : ℝ)^65 ≤ (24986075981049/50000000000000 : ℝ)^49 := by
    have hnat : (2963857403 : ℕ)^65*50000000000000^49 ≤ 24986075981049^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963857403 5000000000 24986075981049 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237967217/625000000 : ℝ)^65 ≤ (27778084483777/100000000000000 : ℝ)^49 := by
    have hnat : (237967217 : ℕ)^65*100000000000000^49 ≤ 27778084483777^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237967217 625000000 27778084483777 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3220948367/10000000000 : ℝ)^65 ≤ (4449952707983/20000000000000 : ℝ)^49 := by
    have hnat : (3220948367 : ℕ)^65*20000000000000^49 ≤ 4449952707983^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3220948367 10000000000 4449952707983 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2963857403/5000000000 : ℝ), (237967217/625000000 : ℝ), (3220948367/10000000000 : ℝ)] ![(24986075981049/50000000000000 : ℝ), (27778084483777/100000000000000 : ℝ), (4449952707983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2963857403/5000000000 : ℝ)|^65 ≤ (24986075981049/50000000000000 : ℝ)^49
        have hw : |(2963857403/5000000000 : ℝ)|=(2963857403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(237967217/625000000 : ℝ)|^65 ≤ (27778084483777/100000000000000 : ℝ)^49
        have hw : |(237967217/625000000 : ℝ)|=(237967217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3220948367/10000000000 : ℝ)|^65 ≤ (4449952707983/20000000000000 : ℝ)^49
        have hw : |(3220948367/10000000000 : ℝ)|=(3220948367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1160801407/2500000000 : ℝ)*x 0 + (-2386738127/5000000000 : ℝ)*x 1 + (-732060059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1160801407/2500000000 : ℝ)^65 ≤ (36142964208487/100000000000000 : ℝ)^49 := by
    have hnat : (1160801407 : ℕ)^65*100000000000000^49 ≤ 36142964208487^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160801407 2500000000 36142964208487 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2386738127/5000000000 : ℝ)^65 ≤ (37494234057797/100000000000000 : ℝ)^49 := by
    have hnat : (2386738127 : ℕ)^65*100000000000000^49 ≤ 37494234057797^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386738127 5000000000 37494234057797 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (732060059/2000000000 : ℝ)^65 ≤ (13181400857681/50000000000000 : ℝ)^49 := by
    have hnat : (732060059 : ℕ)^65*50000000000000^49 ≤ 13181400857681^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732060059 2000000000 13181400857681 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1160801407/2500000000 : ℝ), (-2386738127/5000000000 : ℝ), (-732060059/2000000000 : ℝ)] ![(36142964208487/100000000000000 : ℝ), (37494234057797/100000000000000 : ℝ), (13181400857681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1160801407/2500000000 : ℝ)|^65 ≤ (36142964208487/100000000000000 : ℝ)^49
        have hw : |(1160801407/2500000000 : ℝ)|=(1160801407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2386738127/5000000000 : ℝ)|^65 ≤ (37494234057797/100000000000000 : ℝ)^49
        have hw : |(-2386738127/5000000000 : ℝ)|=(2386738127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-732060059/2000000000 : ℝ)|^65 ≤ (13181400857681/50000000000000 : ℝ)^49
        have hw : |(-732060059/2000000000 : ℝ)|=(732060059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (869349951/2000000000 : ℝ)*x 0 + (-858448459/10000000000 : ℝ)*x 1 + (706180949/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869349951/2000000000 : ℝ)^65 ≤ (33114203710681/100000000000000 : ℝ)^49 := by
    have hnat : (869349951 : ℕ)^65*100000000000000^49 ≤ 33114203710681^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869349951 2000000000 33114203710681 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (858448459/10000000000 : ℝ)^65 ≤ (962674099111/25000000000000 : ℝ)^49 := by
    have hnat : (858448459 : ℕ)^65*25000000000000^49 ≤ 962674099111^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858448459 10000000000 962674099111 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706180949/1000000000 : ℝ)^65 ≤ (63035099873329/100000000000000 : ℝ)^49 := by
    have hnat : (706180949 : ℕ)^65*100000000000000^49 ≤ 63035099873329^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706180949 1000000000 63035099873329 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869349951/2000000000 : ℝ), (-858448459/10000000000 : ℝ), (706180949/1000000000 : ℝ)] ![(33114203710681/100000000000000 : ℝ), (962674099111/25000000000000 : ℝ), (63035099873329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869349951/2000000000 : ℝ)|^65 ≤ (33114203710681/100000000000000 : ℝ)^49
        have hw : |(869349951/2000000000 : ℝ)|=(869349951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-858448459/10000000000 : ℝ)|^65 ≤ (962674099111/25000000000000 : ℝ)^49
        have hw : |(-858448459/10000000000 : ℝ)|=(858448459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(706180949/1000000000 : ℝ)|^65 ≤ (63035099873329/100000000000000 : ℝ)^49
        have hw : |(706180949/1000000000 : ℝ)|=(706180949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1022749083/5000000000 : ℝ)*x 0 + (-2762773971/5000000000 : ℝ)*x 1 + (2613507753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022749083/5000000000 : ℝ)^65 ≤ (97463922931/800000000000 : ℝ)^49 := by
    have hnat : (1022749083 : ℕ)^65*800000000000^49 ≤ 97463922931^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022749083 5000000000 97463922931 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2762773971/5000000000 : ℝ)^65 ≤ (711333141359/1562500000000 : ℝ)^49 := by
    have hnat : (2762773971 : ℕ)^65*1562500000000^49 ≤ 711333141359^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762773971 5000000000 711333141359 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613507753/5000000000 : ℝ)^65 ≤ (42291688571641/100000000000000 : ℝ)^49 := by
    have hnat : (2613507753 : ℕ)^65*100000000000000^49 ≤ 42291688571641^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613507753 5000000000 42291688571641 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1022749083/5000000000 : ℝ), (-2762773971/5000000000 : ℝ), (2613507753/5000000000 : ℝ)] ![(97463922931/800000000000 : ℝ), (711333141359/1562500000000 : ℝ), (42291688571641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1022749083/5000000000 : ℝ)|^65 ≤ (97463922931/800000000000 : ℝ)^49
        have hw : |(-1022749083/5000000000 : ℝ)|=(1022749083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2762773971/5000000000 : ℝ)|^65 ≤ (711333141359/1562500000000 : ℝ)^49
        have hw : |(-2762773971/5000000000 : ℝ)|=(2762773971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613507753/5000000000 : ℝ)|^65 ≤ (42291688571641/100000000000000 : ℝ)^49
        have hw : |(2613507753/5000000000 : ℝ)|=(2613507753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (242930089/400000000 : ℝ)*x 0 + (1936805789/5000000000 : ℝ)*x 1 + (371164153/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (242930089/400000000 : ℝ)^65 ≤ (51606184212301/100000000000000 : ℝ)^49 := by
    have hnat : (242930089 : ℕ)^65*100000000000000^49 ≤ 51606184212301^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242930089 400000000 51606184212301 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1936805789/5000000000 : ℝ)^65 ≤ (14209976599237/50000000000000 : ℝ)^49 := by
    have hnat : (1936805789 : ℕ)^65*50000000000000^49 ≤ 14209976599237^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936805789 5000000000 14209976599237 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (371164153/1250000000 : ℝ)^65 ≤ (1997386256683/10000000000000 : ℝ)^49 := by
    have hnat : (371164153 : ℕ)^65*10000000000000^49 ≤ 1997386256683^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371164153 1250000000 1997386256683 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(242930089/400000000 : ℝ), (1936805789/5000000000 : ℝ), (371164153/1250000000 : ℝ)] ![(51606184212301/100000000000000 : ℝ), (14209976599237/50000000000000 : ℝ), (1997386256683/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(242930089/400000000 : ℝ)|^65 ≤ (51606184212301/100000000000000 : ℝ)^49
        have hw : |(242930089/400000000 : ℝ)|=(242930089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1936805789/5000000000 : ℝ)|^65 ≤ (14209976599237/50000000000000 : ℝ)^49
        have hw : |(1936805789/5000000000 : ℝ)|=(1936805789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(371164153/1250000000 : ℝ)|^65 ≤ (1997386256683/10000000000000 : ℝ)^49
        have hw : |(371164153/1250000000 : ℝ)|=(371164153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4788743473/10000000000 : ℝ)*x 0 + (-197608487/400000000 : ℝ)*x 1 + (-207116907/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4788743473/10000000000 : ℝ)^65 ≤ (9413348474021/25000000000000 : ℝ)^49 := by
    have hnat : (4788743473 : ℕ)^65*25000000000000^49 ≤ 9413348474021^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4788743473 10000000000 9413348474021 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197608487/400000000 : ℝ)^65 ≤ (19620685195617/50000000000000 : ℝ)^49 := by
    have hnat : (197608487 : ℕ)^65*50000000000000^49 ≤ 19620685195617^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197608487 400000000 19620685195617 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207116907/625000000 : ℝ)^65 ≤ (722038615289/3125000000000 : ℝ)^49 := by
    have hnat : (207116907 : ℕ)^65*3125000000000^49 ≤ 722038615289^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207116907 625000000 722038615289 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4788743473/10000000000 : ℝ), (-197608487/400000000 : ℝ), (-207116907/625000000 : ℝ)] ![(9413348474021/25000000000000 : ℝ), (19620685195617/50000000000000 : ℝ), (722038615289/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4788743473/10000000000 : ℝ)|^65 ≤ (9413348474021/25000000000000 : ℝ)^49
        have hw : |(4788743473/10000000000 : ℝ)|=(4788743473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-197608487/400000000 : ℝ)|^65 ≤ (19620685195617/50000000000000 : ℝ)^49
        have hw : |(-197608487/400000000 : ℝ)|=(197608487/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207116907/625000000 : ℝ)|^65 ≤ (722038615289/3125000000000 : ℝ)^49
        have hw : |(-207116907/625000000 : ℝ)|=(207116907/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2152865679/5000000000 : ℝ)*x 0 + (-482353517/5000000000 : ℝ)*x 1 + (7042305919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152865679/5000000000 : ℝ)^65 ≤ (6540064712589/20000000000000 : ℝ)^49 := by
    have hnat : (2152865679 : ℕ)^65*20000000000000^49 ≤ 6540064712589^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152865679 5000000000 6540064712589 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482353517/5000000000 : ℝ)^65 ≤ (2247705831647/50000000000000 : ℝ)^49 := by
    have hnat : (482353517 : ℕ)^65*50000000000000^49 ≤ 2247705831647^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482353517 5000000000 2247705831647 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7042305919/10000000000 : ℝ)^65 ≤ (62804264763229/100000000000000 : ℝ)^49 := by
    have hnat : (7042305919 : ℕ)^65*100000000000000^49 ≤ 62804264763229^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7042305919 10000000000 62804264763229 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152865679/5000000000 : ℝ), (-482353517/5000000000 : ℝ), (7042305919/10000000000 : ℝ)] ![(6540064712589/20000000000000 : ℝ), (2247705831647/50000000000000 : ℝ), (62804264763229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152865679/5000000000 : ℝ)|^65 ≤ (6540064712589/20000000000000 : ℝ)^49
        have hw : |(2152865679/5000000000 : ℝ)|=(2152865679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-482353517/5000000000 : ℝ)|^65 ≤ (2247705831647/50000000000000 : ℝ)^49
        have hw : |(-482353517/5000000000 : ℝ)|=(482353517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7042305919/10000000000 : ℝ)|^65 ≤ (62804264763229/100000000000000 : ℝ)^49
        have hw : |(7042305919/10000000000 : ℝ)|=(7042305919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-753841/4000000 : ℝ)*x 0 + (-6033225309/10000000000 : ℝ)*x 1 + (4813908877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (753841/4000000 : ℝ)^65 ≤ (5464203091369/50000000000000 : ℝ)^49 := by
    have hnat : (753841 : ℕ)^65*50000000000000^49 ≤ 5464203091369^49*4000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753841 4000000 5464203091369 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6033225309/10000000000 : ℝ)^65 ≤ (5115549041943/10000000000000 : ℝ)^49 := by
    have hnat : (6033225309 : ℕ)^65*10000000000000^49 ≤ 5115549041943^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6033225309 10000000000 5115549041943 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4813908877/10000000000 : ℝ)^65 ≤ (37916103382333/100000000000000 : ℝ)^49 := by
    have hnat : (4813908877 : ℕ)^65*100000000000000^49 ≤ 37916103382333^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4813908877 10000000000 37916103382333 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-753841/4000000 : ℝ), (-6033225309/10000000000 : ℝ), (4813908877/10000000000 : ℝ)] ![(5464203091369/50000000000000 : ℝ), (5115549041943/10000000000000 : ℝ), (37916103382333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-753841/4000000 : ℝ)|^65 ≤ (5464203091369/50000000000000 : ℝ)^49
        have hw : |(-753841/4000000 : ℝ)|=(753841/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6033225309/10000000000 : ℝ)|^65 ≤ (5115549041943/10000000000000 : ℝ)^49
        have hw : |(-6033225309/10000000000 : ℝ)|=(6033225309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4813908877/10000000000 : ℝ)|^65 ≤ (37916103382333/100000000000000 : ℝ)^49
        have hw : |(4813908877/10000000000 : ℝ)|=(4813908877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6234148099/10000000000 : ℝ)*x 0 + (1820724747/5000000000 : ℝ)*x 1 + (1507890547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6234148099/10000000000 : ℝ)^65 ≤ (26713793549541/50000000000000 : ℝ)^49 := by
    have hnat : (6234148099 : ℕ)^65*50000000000000^49 ≤ 26713793549541^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6234148099 10000000000 26713793549541 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1820724747/5000000000 : ℝ)^65 ≤ (1309142495919/5000000000000 : ℝ)^49 := by
    have hnat : (1820724747 : ℕ)^65*5000000000000^49 ≤ 1309142495919^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820724747 5000000000 1309142495919 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1507890547/5000000000 : ℝ)^65 ≤ (10194781477843/50000000000000 : ℝ)^49 := by
    have hnat : (1507890547 : ℕ)^65*50000000000000^49 ≤ 10194781477843^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507890547 5000000000 10194781477843 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6234148099/10000000000 : ℝ), (1820724747/5000000000 : ℝ), (1507890547/5000000000 : ℝ)] ![(26713793549541/50000000000000 : ℝ), (1309142495919/5000000000000 : ℝ), (10194781477843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6234148099/10000000000 : ℝ)|^65 ≤ (26713793549541/50000000000000 : ℝ)^49
        have hw : |(6234148099/10000000000 : ℝ)|=(6234148099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1820724747/5000000000 : ℝ)|^65 ≤ (1309142495919/5000000000000 : ℝ)^49
        have hw : |(1820724747/5000000000 : ℝ)|=(1820724747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1507890547/5000000000 : ℝ)|^65 ≤ (10194781477843/50000000000000 : ℝ)^49
        have hw : |(1507890547/5000000000 : ℝ)|=(1507890547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4416720651/10000000000 : ℝ)*x 0 + (-4939710459/10000000000 : ℝ)*x 1 + (-3720630901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4416720651/10000000000 : ℝ)^65 ≤ (33823161189233/100000000000000 : ℝ)^49 := by
    have hnat : (4416720651 : ℕ)^65*100000000000000^49 ≤ 33823161189233^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416720651 10000000000 33823161189233 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4939710459/10000000000 : ℝ)^65 ≤ (4904510488909/12500000000000 : ℝ)^49 := by
    have hnat : (4939710459 : ℕ)^65*12500000000000^49 ≤ 4904510488909^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4939710459 10000000000 4904510488909 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3720630901/10000000000 : ℝ)^65 ≤ (13470377440819/50000000000000 : ℝ)^49 := by
    have hnat : (3720630901 : ℕ)^65*50000000000000^49 ≤ 13470377440819^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3720630901 10000000000 13470377440819 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4416720651/10000000000 : ℝ), (-4939710459/10000000000 : ℝ), (-3720630901/10000000000 : ℝ)] ![(33823161189233/100000000000000 : ℝ), (4904510488909/12500000000000 : ℝ), (13470377440819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4416720651/10000000000 : ℝ)|^65 ≤ (33823161189233/100000000000000 : ℝ)^49
        have hw : |(4416720651/10000000000 : ℝ)|=(4416720651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4939710459/10000000000 : ℝ)|^65 ≤ (4904510488909/12500000000000 : ℝ)^49
        have hw : |(-4939710459/10000000000 : ℝ)|=(4939710459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3720630901/10000000000 : ℝ)|^65 ≤ (13470377440819/50000000000000 : ℝ)^49
        have hw : |(-3720630901/10000000000 : ℝ)|=(3720630901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301076_s3_s3_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5034331989/10000000000 : ℝ)*x 0 + (-962819173/10000000000 : ℝ)*x 1 + (1599102683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5034331989/10000000000 : ℝ)^65 ≤ (1005904499357/2500000000000 : ℝ)^49 := by
    have hnat : (5034331989 : ℕ)^65*2500000000000^49 ≤ 1005904499357^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5034331989 10000000000 1005904499357 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962819173/10000000000 : ℝ)^65 ≤ (4483745649791/100000000000000 : ℝ)^49 := by
    have hnat : (962819173 : ℕ)^65*100000000000000^49 ≤ 4483745649791^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962819173 10000000000 4483745649791 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1599102683/2500000000 : ℝ)^65 ≤ (11056014873743/20000000000000 : ℝ)^49 := by
    have hnat : (1599102683 : ℕ)^65*20000000000000^49 ≤ 11056014873743^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1599102683 2500000000 11056014873743 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5034331989/10000000000 : ℝ), (-962819173/10000000000 : ℝ), (1599102683/2500000000 : ℝ)] ![(1005904499357/2500000000000 : ℝ), (4483745649791/100000000000000 : ℝ), (11056014873743/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5034331989/10000000000 : ℝ)|^65 ≤ (1005904499357/2500000000000 : ℝ)^49
        have hw : |(5034331989/10000000000 : ℝ)|=(5034331989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-962819173/10000000000 : ℝ)|^65 ≤ (4483745649791/100000000000000 : ℝ)^49
        have hw : |(-962819173/10000000000 : ℝ)|=(962819173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1599102683/2500000000 : ℝ)|^65 ≤ (11056014873743/20000000000000 : ℝ)^49
        have hw : |(1599102683/2500000000 : ℝ)|=(1599102683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301076_s3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((67487/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67487/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-18413/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-18413/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2361/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2361/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20109/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20109/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-716/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-716/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13589/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13589/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (67487/100000 : ℝ) ^ (129/32 : ℝ) ≤ (10245039205216511099/50000000000000000000 : ℝ) := by
    have hpowers : (67487/100000 : ℝ)^129 ≤ (10245039205216511099/50000000000000000000 : ℝ)^32 := by
      have hnat : (67487 : ℕ)^129*50000000000000000000^32 ≤ 10245039205216511099^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67487 100000 10245039205216511099 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67487/100000 : ℝ)) (X := (10245039205216511099/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (60245039205216511099/50000000000000000000 : ℝ) ≤ (5236618597307093/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (60245039205216511099/50000000000000000000 : ℝ)^32 ≤ (5236618597307093/5000000000000000 : ℝ)^129 := by
      have hnat : (60245039205216511099 : ℕ)^32*5000000000000000^129 ≤ 5236618597307093^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60245039205216511099 50000000000000000000 5236618597307093 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5236618597307093/5000000000000000 : ℝ)) (X := (60245039205216511099/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (35245039205216511099/25000000000000000000 : ℝ) ≤ (10889311751578603/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (35245039205216511099/25000000000000000000 : ℝ)^32 ≤ (10889311751578603/10000000000000000 : ℝ)^129 := by
      have hnat : (35245039205216511099 : ℕ)^32*10000000000000000^129 ≤ 10889311751578603^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35245039205216511099 25000000000000000000 10889311751578603 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10889311751578603/10000000000000000 : ℝ)) (X := (35245039205216511099/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(236618597307093/3374350000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(416074556964417/6748700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (67487/100000 : ℝ)) (alpha := (236618597307093/3374350000000000 : ℝ)) (beta := (416074556964417/6748700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (67487/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(236618597307093/3374350000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(416074556964417/6748700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (18413/25000 : ℝ) ^ (129/32 : ℝ) ≤ (5829317236269319991/20000000000000000000 : ℝ) := by
    have hpowers : (18413/25000 : ℝ)^129 ≤ (5829317236269319991/20000000000000000000 : ℝ)^32 := by
      have hnat : (18413 : ℕ)^129*20000000000000000000^32 ≤ 5829317236269319991^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18413 25000 5829317236269319991 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18413/25000 : ℝ)) (X := (5829317236269319991/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (25829317236269319991/20000000000000000000 : ℝ) ≤ (10655049107898449/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25829317236269319991/20000000000000000000 : ℝ)^32 ≤ (10655049107898449/10000000000000000 : ℝ)^129 := by
      have hnat : (25829317236269319991 : ℕ)^32*10000000000000000^129 ≤ 10655049107898449^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25829317236269319991 20000000000000000000 10655049107898449 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10655049107898449/10000000000000000 : ℝ)) (X := (25829317236269319991/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (15829317236269319991/10000000000000000000 : ℝ) ≤ (2801683031313197/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (15829317236269319991/10000000000000000000 : ℝ)^32 ≤ (2801683031313197/2500000000000000 : ℝ)^129 := by
      have hnat : (15829317236269319991 : ℕ)^32*2500000000000000^129 ≤ 2801683031313197^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15829317236269319991 10000000000000000000 2801683031313197 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2801683031313197/2500000000000000 : ℝ)) (X := (15829317236269319991/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(655049107898449/7365200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(551683017354339/7365200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (18413/25000 : ℝ)) (alpha := (655049107898449/7365200000000000 : ℝ)) (beta := (551683017354339/7365200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (18413/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(655049107898449/7365200000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(551683017354339/7365200000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (2361/3125 : ℝ) ^ (129/32 : ℝ) ≤ (32298254180038105613/100000000000000000000 : ℝ) := by
    have hpowers : (2361/3125 : ℝ)^129 ≤ (32298254180038105613/100000000000000000000 : ℝ)^32 := by
      have hnat : (2361 : ℕ)^129*100000000000000000000^32 ≤ 32298254180038105613^32*3125^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2361 3125 32298254180038105613 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2361/3125 : ℝ)) (X := (32298254180038105613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (132298254180038105613/100000000000000000000 : ℝ) ≤ (5359483801613231/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (132298254180038105613/100000000000000000000 : ℝ)^32 ≤ (5359483801613231/5000000000000000 : ℝ)^129 := by
      have hnat : (132298254180038105613 : ℕ)^32*5000000000000000^129 ≤ 5359483801613231^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        132298254180038105613 100000000000000000000 5359483801613231 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5359483801613231/5000000000000000 : ℝ)) (X := (132298254180038105613/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (82298254180038105613/50000000000000000000 : ℝ) ≤ (1414476536549527/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (82298254180038105613/50000000000000000000 : ℝ)^32 ≤ (1414476536549527/1250000000000000 : ℝ)^129 := by
      have hnat : (82298254180038105613 : ℕ)^32*1250000000000000^129 ≤ 1414476536549527^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82298254180038105613 50000000000000000000 1414476536549527 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1414476536549527/1250000000000000 : ℝ)) (X := (82298254180038105613/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(119827933871077/1259200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(298422344584877/3777600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (2361/3125 : ℝ)) (alpha := (119827933871077/1259200000000000 : ℝ)) (beta := (298422344584877/3777600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2361/3125 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(119827933871077/1259200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(298422344584877/3777600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-453787657/2000000000 : ℝ)*X 0 0+(-566151643/1000000000 : ℝ)*X 0 1+(1229407411/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((5842411111/10000000000 : ℝ)*X 1 0+(979641747/2500000000 : ℝ)*X 1 1+(1603456417/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((4747387547/10000000000 : ℝ)*X 0 0+(-324845813/2500000000 : ℝ)*X 0 1+(1617036659/2500000000 : ℝ)*X 0 2+(4747387547/10000000000 : ℝ)*X 1 0+(-324845813/2500000000 : ℝ)*X 1 1+(1617036659/2500000000 : ℝ)*X 1 2+(4747387547/10000000000 : ℝ)*X 2 0+(-324845813/2500000000 : ℝ)*X 2 1+(1617036659/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1033221267/5000000000 : ℝ)*X 0 0+(-6086725221/10000000000 : ℝ)*X 0 1+(230949589/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2963857403/5000000000 : ℝ)*X 1 0+(237967217/625000000 : ℝ)*X 1 1+(3220948367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((1160801407/2500000000 : ℝ)*X 2 0+(-2386738127/5000000000 : ℝ)*X 2 1+(-732060059/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((869349951/2000000000 : ℝ)*X 0 0+(-858448459/10000000000 : ℝ)*X 0 1+(706180949/1000000000 : ℝ)*X 0 2+(869349951/2000000000 : ℝ)*X 1 0+(-858448459/10000000000 : ℝ)*X 1 1+(706180949/1000000000 : ℝ)*X 1 2+(869349951/2000000000 : ℝ)*X 2 0+(-858448459/10000000000 : ℝ)*X 2 1+(706180949/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1022749083/5000000000 : ℝ)*X 0 0+(-2762773971/5000000000 : ℝ)*X 0 1+(2613507753/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((242930089/400000000 : ℝ)*X 1 0+(1936805789/5000000000 : ℝ)*X 1 1+(371164153/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((4788743473/10000000000 : ℝ)*X 2 0+(-197608487/400000000 : ℝ)*X 2 1+(-207116907/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((2152865679/5000000000 : ℝ)*X 0 0+(-482353517/5000000000 : ℝ)*X 0 1+(7042305919/10000000000 : ℝ)*X 0 2+(2152865679/5000000000 : ℝ)*X 1 0+(-482353517/5000000000 : ℝ)*X 1 1+(7042305919/10000000000 : ℝ)*X 1 2+(2152865679/5000000000 : ℝ)*X 2 0+(-482353517/5000000000 : ℝ)*X 2 1+(7042305919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-753841/4000000 : ℝ)*X 0 0+(-6033225309/10000000000 : ℝ)*X 0 1+(4813908877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((6234148099/10000000000 : ℝ)*X 1 0+(1820724747/5000000000 : ℝ)*X 1 1+(1507890547/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4416720651/10000000000 : ℝ)*X 2 0+(-4939710459/10000000000 : ℝ)*X 2 1+(-3720630901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((5034331989/10000000000 : ℝ)*X 0 0+(-962819173/10000000000 : ℝ)*X 0 1+(1599102683/2500000000 : ℝ)*X 0 2+(5034331989/10000000000 : ℝ)*X 1 0+(-962819173/10000000000 : ℝ)*X 1 1+(1599102683/2500000000 : ℝ)*X 1 2+(5034331989/10000000000 : ℝ)*X 2 0+(-962819173/10000000000 : ℝ)*X 2 1+(1599102683/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301076_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((20109/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20109/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6390482703594219719892597501/628910745400000000000000000000000 : ℝ) := by norm_num
    linear_combination (961862126677/500000000000 : ℝ)*(base40) + (1535637/500000000000 : ℝ)*(base49) + (1535319/1000000000000 : ℝ)*(base50) + (696060146151/1000000000000 : ℝ)*(base59) + (3047492775603/250000000000 : ℝ)*(major_s3_0) + (3047492775603/250000000000 : ℝ)*(major_s3_1) + (3047492775603/250000000000 : ℝ)*(major_s3_2) + (100634041/1000000000000 : ℝ)*(sp_s3_0) + (245312797/500000000000 : ℝ)*(sp_s3_1) + (16139139512497/1000000000000 : ℝ)*(sp_s3_7) + (16138749520943/1000000000000 : ℝ)*(sp_s3_8) + (16139031889003/1000000000000 : ℝ)*(sp_s3_9) + (4120349335609/500000000000 : ℝ)*(sp_s3_13) + (41651507/200000000000 : ℝ)*(sp_s3_23) + (4120349335609/500000000000 : ℝ)*(f.failure) + (8069620073269/500000000000 : ℝ)*(f.sum) + (248063648843171393/5796412400000000000000000000000 : ℝ)*base62 + (225596626278197/314800000000000000000000000 : ℝ)*base65 + (288686243751173/1841300000000000000000000000 : ℝ)*base66 + (3928558773071/314800000000000000000000000 : ℝ)*base69 + (17449318036735983/169959260800000000000000000000 : ℝ)*base71 + (601243560548707/3374350000000000000000000000 : ℝ)*base73 + (950264711096087/1841300000000000000000000000 : ℝ)*base74 + (236830985280531/3374350000000000000000000000 : ℝ)*base77 + (94371899121956449841/124263813100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (6429/12500000000000000 : ℝ)*base87 + (6429/12500000000000000 : ℝ)*base89 + (6429/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-716/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-716/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2607876531204837004208511/265561345000000000000000000000 : ℝ) := by norm_num
    linear_combination (2430427084873/1000000000000 : ℝ)*(base40) + (66980958331/50000000000 : ℝ)*(base59) + (844577/1000000000000 : ℝ)*(base60) + (157864287851/12500000000 : ℝ)*(major_s3_0) + (157864287851/12500000000 : ℝ)*(major_s3_1) + (157864287851/12500000000 : ℝ)*(major_s3_2) + (18044241/200000000000 : ℝ)*(sp_s3_0) + (20081941/500000000000 : ℝ)*(sp_s3_6) + (270046407/1000000000000 : ℝ)*(sp_s3_8) + (8360301822777/500000000000 : ℝ)*(sp_s3_14) + (16720149347733/1000000000000 : ℝ)*(sp_s3_15) + (16720693866759/1000000000000 : ℝ)*(sp_s3_16) + (4268774376051/500000000000 : ℝ)*(sp_s3_20) + (13723631/50000000000 : ℝ)*(sp_s3_22) + (533599307249/62500000000 : ℝ)*(f.failure) + (16720693866759/1000000000000 : ℝ)*(f.sum) + (59398211114036743/289820620000000000000000000000 : ℝ)*base62 + (5767647284827/47220000000000000000000000 : ℝ)*base65 + (2259396460461/46032500000000000000000000 : ℝ)*base66 + (10934951739431/15740000000000000000000000 : ℝ)*base68 + (1212805166041542979/3186736140000000000000000000000 : ℝ)*base70 + (74587685501661/674870000000000000000000000 : ℝ)*base72 + (4090537174521/184130000000000000000000000 : ℝ)*base75 + (212507651915453/674870000000000000000000000 : ℝ)*base76 + (334442854404019063/3106595327500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (269/1562500000000000 : ℝ)*base87 + (269/1562500000000000 : ℝ)*base89 + (269/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13589/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13589/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6565629274449901884324219/1553297663750000000000000000000 : ℝ) := by norm_num
    linear_combination (1186549/500000000000 : ℝ)*(base3) + (2987391861253/1000000000000 : ℝ)*(base40) + (511991/250000000000 : ℝ)*(base49) + (101208812103/125000000000 : ℝ)*(base59) + (708644673867/50000000000 : ℝ)*(major_s3_0) + (708644673867/50000000000 : ℝ)*(major_s3_1) + (708644673867/50000000000 : ℝ)*(major_s3_2) + (17770543/1000000000000 : ℝ)*(sp_s3_0) + (22938947/500000000000 : ℝ)*(sp_s3_6) + (6384549/250000000000 : ℝ)*(sp_s3_7) + (9382271392497/500000000000 : ℝ)*(sp_s3_21) + (1876458846683/100000000000 : ℝ)*(sp_s3_22) + (4691146523433/250000000000 : ℝ)*(sp_s3_23) + (1197643900123/125000000000 : ℝ)*(sp_s3_27) + (383247978079/40000000000 : ℝ)*(f.failure) + (4691146523433/250000000000 : ℝ)*(f.sum) + (451006635793982857/1159282480000000000000000000000 : ℝ)*base62 + (2947490203233/12592000000000000000000000 : ℝ)*base65 + (127363051942049/368260000000000000000000000 : ℝ)*base66 + (46028785803/12592000000000000000000000 : ℝ)*base69 + (349095229401592257/849796304000000000000000000000 : ℝ)*base70 + (135612140675337/337435000000000000000000000 : ℝ)*base73 + (62183645466589/368260000000000000000000000 : ℝ)*base74 + (3256100461763/4217937500000000000000000 : ℝ)*base76 + (2329571868655488169/24852762620000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (501/1000000000000000 : ℝ)*base86 + (501/1000000000000000 : ℝ)*base88 + (501/1000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((67487/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67487/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-18413/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-18413/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2361/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2361/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20109/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20109/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-716/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-716/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13589/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13589/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301076_s3 p hpa hpb X hX hprev2

#print axioms solution
