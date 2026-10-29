-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c319086_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:31:37.173205+00:00
-- url     : https://prove2.me/submissions/cd1e35e7-4c6d-4cf4-ac9b-8bcec716d59d

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
theorem collision_support_c319086_s0_s0_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (6319209079/10000000000 : ℝ)*x 0 + (605567469/2000000000 : ℝ)*x 1 + (2890940021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6319209079/10000000000 : ℝ)^5 ≤ (28170750051637/50000000000000 : ℝ)^4 := by
    have hnat : (6319209079 : ℕ)^5*50000000000000^4 ≤ 28170750051637^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6319209079 10000000000 28170750051637 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605567469/2000000000 : ℝ)^5 ≤ (11230153199381/50000000000000 : ℝ)^4 := by
    have hnat : (605567469 : ℕ)^5*50000000000000^4 ≤ 11230153199381^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605567469 2000000000 11230153199381 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2890940021/10000000000 : ℝ)^5 ≤ (21198193478499/100000000000000 : ℝ)^4 := by
    have hnat : (2890940021 : ℕ)^5*100000000000000^4 ≤ 21198193478499^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2890940021 10000000000 21198193478499 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6319209079/10000000000 : ℝ), (605567469/2000000000 : ℝ), (2890940021/10000000000 : ℝ)] ![(28170750051637/50000000000000 : ℝ), (11230153199381/50000000000000 : ℝ), (21198193478499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6319209079/10000000000 : ℝ)|^5 ≤ (28170750051637/50000000000000 : ℝ)^4
        have hw : |(6319209079/10000000000 : ℝ)|=(6319209079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605567469/2000000000 : ℝ)|^5 ≤ (11230153199381/50000000000000 : ℝ)^4
        have hw : |(605567469/2000000000 : ℝ)|=(605567469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2890940021/10000000000 : ℝ)|^5 ≤ (21198193478499/100000000000000 : ℝ)^4
        have hw : |(2890940021/10000000000 : ℝ)|=(2890940021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2976545873/5000000000 : ℝ)*x 0 + (-1645685433/5000000000 : ℝ)*x 1 + (-38276877/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2976545873/5000000000 : ℝ)^5 ≤ (51065579301/97656250000 : ℝ)^4 := by
    have hnat : (2976545873 : ℕ)^5*97656250000^4 ≤ 51065579301^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2976545873 5000000000 51065579301 97656250000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1645685433/5000000000 : ℝ)^5 ≤ (6232482022033/25000000000000 : ℝ)^4 := by
    have hnat : (1645685433 : ℕ)^5*25000000000000^4 ≤ 6232482022033^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645685433 5000000000 6232482022033 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38276877/125000000 : ℝ)^5 ≤ (2847364836859/12500000000000 : ℝ)^4 := by
    have hnat : (38276877 : ℕ)^5*12500000000000^4 ≤ 2847364836859^4*125000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38276877 125000000 2847364836859 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2976545873/5000000000 : ℝ), (-1645685433/5000000000 : ℝ), (-38276877/125000000 : ℝ)] ![(51065579301/97656250000 : ℝ), (6232482022033/25000000000000 : ℝ), (2847364836859/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2976545873/5000000000 : ℝ)|^5 ≤ (51065579301/97656250000 : ℝ)^4
        have hw : |(2976545873/5000000000 : ℝ)|=(2976545873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1645685433/5000000000 : ℝ)|^5 ≤ (6232482022033/25000000000000 : ℝ)^4
        have hw : |(-1645685433/5000000000 : ℝ)|=(1645685433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38276877/125000000 : ℝ)|^5 ≤ (2847364836859/12500000000000 : ℝ)^4
        have hw : |(-38276877/125000000 : ℝ)|=(38276877/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (701168571/2000000000 : ℝ)*x 0 + (-1086993383/5000000000 : ℝ)*x 1 + (12663101/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (701168571/2000000000 : ℝ)^5 ≤ (26976807744387/100000000000000 : ℝ)^4 := by
    have hnat : (701168571 : ℕ)^5*100000000000000^4 ≤ 26976807744387^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701168571 2000000000 26976807744387 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086993383/5000000000 : ℝ)^5 ≤ (14844689566607/100000000000000 : ℝ)^4 := by
    have hnat : (1086993383 : ℕ)^5*100000000000000^4 ≤ 14844689566607^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086993383 5000000000 14844689566607 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12663101/19531250 : ℝ)^5 ≤ (58178502671871/100000000000000 : ℝ)^4 := by
    have hnat : (12663101 : ℕ)^5*100000000000000^4 ≤ 58178502671871^4*19531250^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12663101 19531250 58178502671871 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(701168571/2000000000 : ℝ), (-1086993383/5000000000 : ℝ), (12663101/19531250 : ℝ)] ![(26976807744387/100000000000000 : ℝ), (14844689566607/100000000000000 : ℝ), (58178502671871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(701168571/2000000000 : ℝ)|^5 ≤ (26976807744387/100000000000000 : ℝ)^4
        have hw : |(701168571/2000000000 : ℝ)|=(701168571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1086993383/5000000000 : ℝ)|^5 ≤ (14844689566607/100000000000000 : ℝ)^4
        have hw : |(-1086993383/5000000000 : ℝ)|=(1086993383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12663101/19531250 : ℝ)|^5 ≤ (58178502671871/100000000000000 : ℝ)^4
        have hw : |(12663101/19531250 : ℝ)|=(12663101/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (119/500000000 : ℝ)*x 0 + (-8534975431/10000000000 : ℝ)*x 1 + (2532377173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119/500000000 : ℝ)^5 ≤ (6571/1250000000000 : ℝ)^4 := by
    have hnat : (119 : ℕ)^5*1250000000000^4 ≤ 6571^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119 500000000 6571 1250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8534975431/10000000000 : ℝ)^5 ≤ (82035691665407/100000000000000 : ℝ)^4 := by
    have hnat : (8534975431 : ℕ)^5*100000000000000^4 ≤ 82035691665407^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8534975431 10000000000 82035691665407 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2532377173/10000000000 : ℝ)^5 ≤ (17964307799709/100000000000000 : ℝ)^4 := by
    have hnat : (2532377173 : ℕ)^5*100000000000000^4 ≤ 17964307799709^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532377173 10000000000 17964307799709 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(119/500000000 : ℝ), (-8534975431/10000000000 : ℝ), (2532377173/10000000000 : ℝ)] ![(6571/1250000000000 : ℝ), (82035691665407/100000000000000 : ℝ), (17964307799709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(119/500000000 : ℝ)|^5 ≤ (6571/1250000000000 : ℝ)^4
        have hw : |(119/500000000 : ℝ)|=(119/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8534975431/10000000000 : ℝ)|^5 ≤ (82035691665407/100000000000000 : ℝ)^4
        have hw : |(-8534975431/10000000000 : ℝ)|=(8534975431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2532377173/10000000000 : ℝ)|^5 ≤ (17964307799709/100000000000000 : ℝ)^4
        have hw : |(2532377173/10000000000 : ℝ)|=(2532377173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (549377729/1250000000 : ℝ)*x 0 + (5771030233/10000000000 : ℝ)*x 1 + (2064380547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549377729/1250000000 : ℝ)^5 ≤ (8946255652151/25000000000000 : ℝ)^4 := by
    have hnat : (549377729 : ℕ)^5*25000000000000^4 ≤ 8946255652151^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549377729 1250000000 8946255652151 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5771030233/10000000000 : ℝ)^5 ≤ (12574962410349/25000000000000 : ℝ)^4 := by
    have hnat : (5771030233 : ℕ)^5*25000000000000^4 ≤ 12574962410349^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5771030233 10000000000 12574962410349 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064380547/10000000000 : ℝ)^5 ≤ (1391512774003/10000000000000 : ℝ)^4 := by
    have hnat : (2064380547 : ℕ)^5*10000000000000^4 ≤ 1391512774003^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064380547 10000000000 1391512774003 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(549377729/1250000000 : ℝ), (5771030233/10000000000 : ℝ), (2064380547/10000000000 : ℝ)] ![(8946255652151/25000000000000 : ℝ), (12574962410349/25000000000000 : ℝ), (1391512774003/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(549377729/1250000000 : ℝ)|^5 ≤ (8946255652151/25000000000000 : ℝ)^4
        have hw : |(549377729/1250000000 : ℝ)|=(549377729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5771030233/10000000000 : ℝ)|^5 ≤ (12574962410349/25000000000000 : ℝ)^4
        have hw : |(5771030233/10000000000 : ℝ)|=(5771030233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064380547/10000000000 : ℝ)|^5 ≤ (1391512774003/10000000000000 : ℝ)^4
        have hw : |(2064380547/10000000000 : ℝ)|=(2064380547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1383819239/2000000000 : ℝ)*x 0 + (-153718559/625000000 : ℝ)*x 1 + (-2712437073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1383819239/2000000000 : ℝ)^5 ≤ (63104700620229/100000000000000 : ℝ)^4 := by
    have hnat : (1383819239 : ℕ)^5*100000000000000^4 ≤ 63104700620229^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383819239 2000000000 63104700620229 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153718559/625000000 : ℝ)^5 ≤ (17320397672037/100000000000000 : ℝ)^4 := by
    have hnat : (153718559 : ℕ)^5*100000000000000^4 ≤ 17320397672037^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153718559 625000000 17320397672037 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712437073/10000000000 : ℝ)^5 ≤ (19574901684771/100000000000000 : ℝ)^4 := by
    have hnat : (2712437073 : ℕ)^5*100000000000000^4 ≤ 19574901684771^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712437073 10000000000 19574901684771 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1383819239/2000000000 : ℝ), (-153718559/625000000 : ℝ), (-2712437073/10000000000 : ℝ)] ![(63104700620229/100000000000000 : ℝ), (17320397672037/100000000000000 : ℝ), (19574901684771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1383819239/2000000000 : ℝ)|^5 ≤ (63104700620229/100000000000000 : ℝ)^4
        have hw : |(1383819239/2000000000 : ℝ)|=(1383819239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-153718559/625000000 : ℝ)|^5 ≤ (17320397672037/100000000000000 : ℝ)^4
        have hw : |(-153718559/625000000 : ℝ)|=(153718559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2712437073/10000000000 : ℝ)|^5 ≤ (19574901684771/100000000000000 : ℝ)^4
        have hw : |(-2712437073/10000000000 : ℝ)|=(2712437073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3236475573/10000000000 : ℝ)*x 0 + (-236747013/10000000000 : ℝ)*x 1 + (15459689/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3236475573/10000000000 : ℝ)^5 ≤ (6102818100317/25000000000000 : ℝ)^4 := by
    have hnat : (3236475573 : ℕ)^5*25000000000000^4 ≤ 6102818100317^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3236475573 10000000000 6102818100317 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236747013/10000000000 : ℝ)^5 ≤ (928657638637/100000000000000 : ℝ)^4 := by
    have hnat : (236747013 : ℕ)^5*100000000000000^4 ≤ 928657638637^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236747013 10000000000 928657638637 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15459689/19531250 : ℝ)^5 ≤ (14932013991143/20000000000000 : ℝ)^4 := by
    have hnat : (15459689 : ℕ)^5*20000000000000^4 ≤ 14932013991143^4*19531250^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15459689 19531250 14932013991143 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3236475573/10000000000 : ℝ), (-236747013/10000000000 : ℝ), (15459689/19531250 : ℝ)] ![(6102818100317/25000000000000 : ℝ), (928657638637/100000000000000 : ℝ), (14932013991143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3236475573/10000000000 : ℝ)|^5 ≤ (6102818100317/25000000000000 : ℝ)^4
        have hw : |(3236475573/10000000000 : ℝ)|=(3236475573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-236747013/10000000000 : ℝ)|^5 ≤ (928657638637/100000000000000 : ℝ)^4
        have hw : |(-236747013/10000000000 : ℝ)|=(236747013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15459689/19531250 : ℝ)|^5 ≤ (14932013991143/20000000000000 : ℝ)^4
        have hw : |(15459689/19531250 : ℝ)|=(15459689/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-865907/10000000000 : ℝ)*x 0 + (-2145183129/5000000000 : ℝ)*x 1 + (3554458119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865907/10000000000 : ℝ)^5 ≤ (417646713/50000000000000 : ℝ)^4 := by
    have hnat : (865907 : ℕ)^5*50000000000000^4 ≤ 417646713^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865907 10000000000 417646713 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145183129/5000000000 : ℝ)^5 ≤ (8680764395363/25000000000000 : ℝ)^4 := by
    have hnat : (2145183129 : ℕ)^5*25000000000000^4 ≤ 8680764395363^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145183129 5000000000 8680764395363 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3554458119/5000000000 : ℝ)^5 ≤ (65276107112311/100000000000000 : ℝ)^4 := by
    have hnat : (3554458119 : ℕ)^5*100000000000000^4 ≤ 65276107112311^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3554458119 5000000000 65276107112311 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-865907/10000000000 : ℝ), (-2145183129/5000000000 : ℝ), (3554458119/5000000000 : ℝ)] ![(417646713/50000000000000 : ℝ), (8680764395363/25000000000000 : ℝ), (65276107112311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-865907/10000000000 : ℝ)|^5 ≤ (417646713/50000000000000 : ℝ)^4
        have hw : |(-865907/10000000000 : ℝ)|=(865907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145183129/5000000000 : ℝ)|^5 ≤ (8680764395363/25000000000000 : ℝ)^4
        have hw : |(-2145183129/5000000000 : ℝ)|=(2145183129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3554458119/5000000000 : ℝ)|^5 ≤ (65276107112311/100000000000000 : ℝ)^4
        have hw : |(3554458119/5000000000 : ℝ)|=(3554458119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2154434601/2500000000 : ℝ)*x 0 + (439434909/2000000000 : ℝ)*x 1 + (424327739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154434601/2500000000 : ℝ)^5 ≤ (4151563047771/5000000000000 : ℝ)^4 := by
    have hnat : (2154434601 : ℕ)^5*5000000000000^4 ≤ 4151563047771^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154434601 2500000000 4151563047771 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (439434909/2000000000 : ℝ)^5 ≤ (3008573974383/20000000000000 : ℝ)^4 := by
    have hnat : (439434909 : ℕ)^5*20000000000000^4 ≤ 3008573974383^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439434909 2000000000 3008573974383 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424327739/10000000000 : ℝ)^5 ≤ (1925869161871/100000000000000 : ℝ)^4 := by
    have hnat : (424327739 : ℕ)^5*100000000000000^4 ≤ 1925869161871^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424327739 10000000000 1925869161871 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154434601/2500000000 : ℝ), (439434909/2000000000 : ℝ), (424327739/10000000000 : ℝ)] ![(4151563047771/5000000000000 : ℝ), (3008573974383/20000000000000 : ℝ), (1925869161871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154434601/2500000000 : ℝ)|^5 ≤ (4151563047771/5000000000000 : ℝ)^4
        have hw : |(2154434601/2500000000 : ℝ)|=(2154434601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(439434909/2000000000 : ℝ)|^5 ≤ (3008573974383/20000000000000 : ℝ)^4
        have hw : |(439434909/2000000000 : ℝ)|=(439434909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424327739/10000000000 : ℝ)|^5 ≤ (1925869161871/100000000000000 : ℝ)^4
        have hw : |(424327739/10000000000 : ℝ)|=(424327739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3999962961/5000000000 : ℝ)*x 0 + (-522631933/2500000000 : ℝ)*x 1 + (-201366109/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3999962961/5000000000 : ℝ)^5 ≤ (37829226494091/50000000000000 : ℝ)^4 := by
    have hnat : (3999962961 : ℕ)^5*50000000000000^4 ≤ 37829226494091^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3999962961 5000000000 37829226494091 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522631933/2500000000 : ℝ)^5 ≤ (883486532509/6250000000000 : ℝ)^4 := by
    have hnat : (522631933 : ℕ)^5*6250000000000^4 ≤ 883486532509^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522631933 2500000000 883486532509 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201366109/1250000000 : ℝ)^5 ≤ (5102881238271/50000000000000 : ℝ)^4 := by
    have hnat : (201366109 : ℕ)^5*50000000000000^4 ≤ 5102881238271^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201366109 1250000000 5102881238271 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3999962961/5000000000 : ℝ), (-522631933/2500000000 : ℝ), (-201366109/1250000000 : ℝ)] ![(37829226494091/50000000000000 : ℝ), (883486532509/6250000000000 : ℝ), (5102881238271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3999962961/5000000000 : ℝ)|^5 ≤ (37829226494091/50000000000000 : ℝ)^4
        have hw : |(3999962961/5000000000 : ℝ)|=(3999962961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-522631933/2500000000 : ℝ)|^5 ≤ (883486532509/6250000000000 : ℝ)^4
        have hw : |(-522631933/2500000000 : ℝ)|=(522631933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201366109/1250000000 : ℝ)|^5 ≤ (5102881238271/50000000000000 : ℝ)^4
        have hw : |(-201366109/1250000000 : ℝ)|=(201366109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (407097607/2000000000 : ℝ)*x 0 + (-1287660899/10000000000 : ℝ)*x 1 + (8249005381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407097607/2000000000 : ℝ)^5 ≤ (1367211467313/10000000000000 : ℝ)^4 := by
    have hnat : (407097607 : ℕ)^5*10000000000000^4 ≤ 1367211467313^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407097607 2000000000 1367211467313 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1287660899/10000000000 : ℝ)^5 ≤ (7713507127907/100000000000000 : ℝ)^4 := by
    have hnat : (1287660899 : ℕ)^5*100000000000000^4 ≤ 7713507127907^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287660899 10000000000 7713507127907 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8249005381/10000000000 : ℝ)^5 ≤ (78614378183213/100000000000000 : ℝ)^4 := by
    have hnat : (8249005381 : ℕ)^5*100000000000000^4 ≤ 78614378183213^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8249005381 10000000000 78614378183213 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(407097607/2000000000 : ℝ), (-1287660899/10000000000 : ℝ), (8249005381/10000000000 : ℝ)] ![(1367211467313/10000000000000 : ℝ), (7713507127907/100000000000000 : ℝ), (78614378183213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(407097607/2000000000 : ℝ)|^5 ≤ (1367211467313/10000000000000 : ℝ)^4
        have hw : |(407097607/2000000000 : ℝ)|=(407097607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1287660899/10000000000 : ℝ)|^5 ≤ (7713507127907/100000000000000 : ℝ)^4
        have hw : |(-1287660899/10000000000 : ℝ)|=(1287660899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8249005381/10000000000 : ℝ)|^5 ≤ (78614378183213/100000000000000 : ℝ)^4
        have hw : |(8249005381/10000000000 : ℝ)|=(8249005381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (8831/5000000000 : ℝ)*x 0 + (-4353817173/5000000000 : ℝ)*x 1 + (1147498421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8831/5000000000 : ℝ)^5 ≤ (257549/4000000000000 : ℝ)^4 := by
    have hnat : (8831 : ℕ)^5*4000000000000^4 ≤ 257549^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8831 5000000000 257549 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4353817173/5000000000 : ℝ)^5 ≤ (42057672413331/50000000000000 : ℝ)^4 := by
    have hnat : (4353817173 : ℕ)^5*50000000000000^4 ≤ 42057672413331^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353817173 5000000000 42057672413331 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147498421/5000000000 : ℝ)^5 ≤ (15884648728871/100000000000000 : ℝ)^4 := by
    have hnat : (1147498421 : ℕ)^5*100000000000000^4 ≤ 15884648728871^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147498421 5000000000 15884648728871 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8831/5000000000 : ℝ), (-4353817173/5000000000 : ℝ), (1147498421/5000000000 : ℝ)] ![(257549/4000000000000 : ℝ), (42057672413331/50000000000000 : ℝ), (15884648728871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8831/5000000000 : ℝ)|^5 ≤ (257549/4000000000000 : ℝ)^4
        have hw : |(8831/5000000000 : ℝ)|=(8831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4353817173/5000000000 : ℝ)|^5 ≤ (42057672413331/50000000000000 : ℝ)^4
        have hw : |(-4353817173/5000000000 : ℝ)|=(4353817173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1147498421/5000000000 : ℝ)|^5 ≤ (15884648728871/100000000000000 : ℝ)^4
        have hw : |(1147498421/5000000000 : ℝ)|=(1147498421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (8679597579/10000000000 : ℝ)*x 0 + (1314419589/10000000000 : ℝ)*x 1 + (1366548953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8679597579/10000000000 : ℝ)^5 ≤ (83776938851229/100000000000000 : ℝ)^4 := by
    have hnat : (8679597579 : ℕ)^5*100000000000000^4 ≤ 83776938851229^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8679597579 10000000000 83776938851229 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314419589/10000000000 : ℝ)^5 ≤ (7914391479983/100000000000000 : ℝ)^4 := by
    have hnat : (1314419589 : ℕ)^5*100000000000000^4 ≤ 7914391479983^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314419589 10000000000 7914391479983 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366548953/10000000000 : ℝ)^5 ≤ (2077167413899/25000000000000 : ℝ)^4 := by
    have hnat : (1366548953 : ℕ)^5*25000000000000^4 ≤ 2077167413899^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366548953 10000000000 2077167413899 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8679597579/10000000000 : ℝ), (1314419589/10000000000 : ℝ), (1366548953/10000000000 : ℝ)] ![(83776938851229/100000000000000 : ℝ), (7914391479983/100000000000000 : ℝ), (2077167413899/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8679597579/10000000000 : ℝ)|^5 ≤ (83776938851229/100000000000000 : ℝ)^4
        have hw : |(8679597579/10000000000 : ℝ)|=(8679597579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314419589/10000000000 : ℝ)|^5 ≤ (7914391479983/100000000000000 : ℝ)^4
        have hw : |(1314419589/10000000000 : ℝ)|=(1314419589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366548953/10000000000 : ℝ)|^5 ≤ (2077167413899/25000000000000 : ℝ)^4
        have hw : |(1366548953/10000000000 : ℝ)|=(1366548953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3263248179/10000000000 : ℝ)*x 0 + (-876142773/2000000000 : ℝ)*x 1 + (-4775320951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3263248179/10000000000 : ℝ)^5 ≤ (4932789990023/20000000000000 : ℝ)^4 := by
    have hnat : (3263248179 : ℕ)^5*20000000000000^4 ≤ 4932789990023^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3263248179 10000000000 4932789990023 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876142773/2000000000 : ℝ)^5 ≤ (2227466219381/6250000000000 : ℝ)^4 := by
    have hnat : (876142773 : ℕ)^5*6250000000000^4 ≤ 2227466219381^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876142773 2000000000 2227466219381 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4775320951/10000000000 : ℝ)^5 ≤ (39696590521089/100000000000000 : ℝ)^4 := by
    have hnat : (4775320951 : ℕ)^5*100000000000000^4 ≤ 39696590521089^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775320951 10000000000 39696590521089 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3263248179/10000000000 : ℝ), (-876142773/2000000000 : ℝ), (-4775320951/10000000000 : ℝ)] ![(4932789990023/20000000000000 : ℝ), (2227466219381/6250000000000 : ℝ), (39696590521089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3263248179/10000000000 : ℝ)|^5 ≤ (4932789990023/20000000000000 : ℝ)^4
        have hw : |(3263248179/10000000000 : ℝ)|=(3263248179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-876142773/2000000000 : ℝ)|^5 ≤ (2227466219381/6250000000000 : ℝ)^4
        have hw : |(-876142773/2000000000 : ℝ)|=(876142773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4775320951/10000000000 : ℝ)|^5 ≤ (39696590521089/100000000000000 : ℝ)^4
        have hw : |(-4775320951/10000000000 : ℝ)|=(4775320951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s0_s0_27 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (144385707/200000000 : ℝ)*x 0 + (-686755697/10000000000 : ℝ)*x 1 + (762114119/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (144385707/200000000 : ℝ)^5 ≤ (16636339282353/25000000000000 : ℝ)^4 := by
    have hnat : (144385707 : ℕ)^5*25000000000000^4 ≤ 16636339282353^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144385707 200000000 16636339282353 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686755697/10000000000 : ℝ)^5 ≤ (878906845761/25000000000000 : ℝ)^4 := by
    have hnat : (686755697 : ℕ)^5*25000000000000^4 ≤ 878906845761^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686755697 10000000000 878906845761 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (762114119/2000000000 : ℝ)^5 ≤ (14969507738277/50000000000000 : ℝ)^4 := by
    have hnat : (762114119 : ℕ)^5*50000000000000^4 ≤ 14969507738277^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762114119 2000000000 14969507738277 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(144385707/200000000 : ℝ), (-686755697/10000000000 : ℝ), (762114119/2000000000 : ℝ)] ![(16636339282353/25000000000000 : ℝ), (878906845761/25000000000000 : ℝ), (14969507738277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(144385707/200000000 : ℝ)|^5 ≤ (16636339282353/25000000000000 : ℝ)^4
        have hw : |(144385707/200000000 : ℝ)|=(144385707/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-686755697/10000000000 : ℝ)|^5 ≤ (878906845761/25000000000000 : ℝ)^4
        have hw : |(-686755697/10000000000 : ℝ)|=(686755697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(762114119/2000000000 : ℝ)|^5 ≤ (14969507738277/50000000000000 : ℝ)^4
        have hw : |(762114119/2000000000 : ℝ)|=(762114119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319086_s0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : (0 : ℝ) ≤ ((31003/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31003/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-74177/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-74177/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9329/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9329/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (17037/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((6319209079/10000000000 : ℝ)*X 1 0+(605567469/2000000000 : ℝ)*X 1 1+(2890940021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2976545873/5000000000 : ℝ)*X 2 0+(-1645685433/5000000000 : ℝ)*X 2 1+(-38276877/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((701168571/2000000000 : ℝ)*X 0 0+(-1086993383/5000000000 : ℝ)*X 0 1+(12663101/19531250 : ℝ)*X 0 2+(701168571/2000000000 : ℝ)*X 1 0+(-1086993383/5000000000 : ℝ)*X 1 1+(12663101/19531250 : ℝ)*X 1 2+(701168571/2000000000 : ℝ)*X 2 0+(-1086993383/5000000000 : ℝ)*X 2 1+(12663101/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((119/500000000 : ℝ)*X 0 0+(-8534975431/10000000000 : ℝ)*X 0 1+(2532377173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((549377729/1250000000 : ℝ)*X 1 0+(5771030233/10000000000 : ℝ)*X 1 1+(2064380547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1383819239/2000000000 : ℝ)*X 2 0+(-153718559/625000000 : ℝ)*X 2 1+(-2712437073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3236475573/10000000000 : ℝ)*X 0 0+(-236747013/10000000000 : ℝ)*X 0 1+(15459689/19531250 : ℝ)*X 0 2+(3236475573/10000000000 : ℝ)*X 1 0+(-236747013/10000000000 : ℝ)*X 1 1+(15459689/19531250 : ℝ)*X 1 2+(3236475573/10000000000 : ℝ)*X 2 0+(-236747013/10000000000 : ℝ)*X 2 1+(15459689/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-865907/10000000000 : ℝ)*X 0 0+(-2145183129/5000000000 : ℝ)*X 0 1+(3554458119/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2154434601/2500000000 : ℝ)*X 1 0+(439434909/2000000000 : ℝ)*X 1 1+(424327739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3999962961/5000000000 : ℝ)*X 2 0+(-522631933/2500000000 : ℝ)*X 2 1+(-201366109/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((407097607/2000000000 : ℝ)*X 0 0+(-1287660899/10000000000 : ℝ)*X 0 1+(8249005381/10000000000 : ℝ)*X 0 2+(407097607/2000000000 : ℝ)*X 1 0+(-1287660899/10000000000 : ℝ)*X 1 1+(8249005381/10000000000 : ℝ)*X 1 2+(407097607/2000000000 : ℝ)*X 2 0+(-1287660899/10000000000 : ℝ)*X 2 1+(8249005381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((8831/5000000000 : ℝ)*X 0 0+(-4353817173/5000000000 : ℝ)*X 0 1+(1147498421/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8679597579/10000000000 : ℝ)*X 1 0+(1314419589/10000000000 : ℝ)*X 1 1+(1366548953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3263248179/10000000000 : ℝ)*X 2 0+(-876142773/2000000000 : ℝ)*X 2 1+(-4775320951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((144385707/200000000 : ℝ)*X 0 0+(-686755697/10000000000 : ℝ)*X 0 1+(762114119/2000000000 : ℝ)*X 0 2+(144385707/200000000 : ℝ)*X 1 0+(-686755697/10000000000 : ℝ)*X 1 1+(762114119/2000000000 : ℝ)*X 1 2+(144385707/200000000 : ℝ)*X 2 0+(-686755697/10000000000 : ℝ)*X 2 1+(762114119/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((31003/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31003/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6098852761660858711929/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (712435486811/1000000000000 : ℝ)*(base7) + (38789349397/500000000000 : ℝ)*(base43) + (658801397271/1000000000000 : ℝ)*(base54) + (835899599141/500000000000 : ℝ)*(major_s0_0) + (49819390609/31250000000 : ℝ)*(major_s0_1) + (1012997801011/1000000000000 : ℝ)*(major_s0_2) + (8532557/100000000000 : ℝ)*(sp_s0_2) + (3521629/250000000000 : ℝ)*(sp_s0_6) + (1958184898357/1000000000000 : ℝ)*(sp_s0_7) + (407157669291/200000000000 : ℝ)*(sp_s0_8) + (1299322924819/1000000000000 : ℝ)*(sp_s0_9) + (478409580759/500000000000 : ℝ)*(sp_s0_13) + (17152289/1000000000000 : ℝ)*(sp_s0_20) + (3093663/125000000000 : ℝ)*(sp_s0_21) + (1764094357/1953125000 : ℝ)*(f.failure) + (407157669291/200000000000 : ℝ)*(f.sum) + (109977170867891/2000000000000000000000000000 : ℝ)*base63 + (2125115667877483/10000000000000000000000000000 : ℝ)*base65 + (128604437819961/312500000000000000000000000 : ℝ)*base67 + (2137776025936481/10000000000000000000000000000 : ℝ)*base68 + (201230663331939/10000000000000000000000000000 : ℝ)*base70 + (2244780342884627/5000000000000000000000000000 : ℝ)*base73 + (24748775178877/312500000000000000000000000 : ℝ)*base74 + (591436354104711/5000000000000000000000000000 : ℝ)*base76 + (1001613311004003/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (839/1562500000000000 : ℝ)*base87 + (839/1562500000000000 : ℝ)*base89 + (839/1562500000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-74177/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-74177/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7268294043407699404263/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (572624743833/500000000000 : ℝ)*(base7) + (263301/250000000000 : ℝ)*(base31) + (41257752617/1000000000000 : ℝ)*(base33) + (4081229651/250000000000 : ℝ)*(base60) + (151479089863/100000000000 : ℝ)*(major_s0_0) + (1556048651247/1000000000000 : ℝ)*(major_s0_1) + (1556048651247/1000000000000 : ℝ)*(major_s0_2) + (5041217/1000000000000 : ℝ)*(sp_s0_1) + (593247/1000000000000 : ℝ)*(sp_s0_9) + (1621027957617/1000000000000 : ℝ)*(sp_s0_14) + (1579740220101/1000000000000 : ℝ)*(sp_s0_15) + (197471201469/125000000000 : ℝ)*(sp_s0_16) + (1985928657077/1000000000000 : ℝ)*(sp_s0_20) + (24943681/1000000000000 : ℝ)*(sp_s0_22) + (168136044523/200000000000 : ℝ)*(f.failure) + (1621027957617/1000000000000 : ℝ)*(f.sum) + (330319056554207/2500000000000000000000000000 : ℝ)*base62 + (7696802971816391/10000000000000000000000000000 : ℝ)*base65 + (7476398770400437/10000000000000000000000000000 : ℝ)*base66 + (839172528400437/10000000000000000000000000000 : ℝ)*base68 + (1123962551162661/10000000000000000000000000000 : ℝ)*base71 + (335727736201439/1000000000000000000000000000 : ℝ)*base72 + (1045987766816391/10000000000000000000000000000 : ℝ)*base74 + (394276763934627/1000000000000000000000000000 : ℝ)*base77 + (452266985414827/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (81/10000000000000000 : ℝ)*base87 + (81/10000000000000000 : ℝ)*base89 + (81/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9329/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9329/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4185203224708998474117/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (245840951361/250000000000 : ℝ)*(base7) + (370671/200000000000 : ℝ)*(base15) + (1996506641/125000000000 : ℝ)*(base40) + (757109121927/1000000000000 : ℝ)*(base43) + (1125037/1000000000000 : ℝ)*(base50) + (1530289863063/1000000000000 : ℝ)*(major_s0_0) + (48323796321/62500000000 : ℝ)*(major_s0_1) + (1530289863063/1000000000000 : ℝ)*(major_s0_2) + (3083453/200000000000 : ℝ)*(sp_s0_2) + (52162129/1000000000000 : ℝ)*(sp_s0_7) + (57387482647/62500000000 : ℝ)*(sp_s0_21) + (837679576527/500000000000 : ℝ)*(sp_s0_22) + (57389779201/62500000000 : ℝ)*(sp_s0_23) + (1810127429907/1000000000000 : ℝ)*(sp_s0_27) + (826763624463/1000000000000 : ℝ)*(f.failure) + (1675361006409/1000000000000 : ℝ)*(f.sum) + (3044728159669181/10000000000000000000000000000 : ℝ)*base62 + (1884265222738961/10000000000000000000000000000 : ℝ)*base64 + (427412913165491/625000000000000000000000000 : ℝ)*base66 + (10359521192102573/10000000000000000000000000000 : ℝ)*base68 + (1253748447920767/5000000000000000000000000000 : ℝ)*base70 + (5580787334261039/10000000000000000000000000000 : ℝ)*base72 + (363223249597913/625000000000000000000000000 : ℝ)*base74 + (3409720967102573/10000000000000000000000000000 : ℝ)*base76 + (760741660181779/2000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (27261/50000000000000000 : ℝ)*base87 + (27261/50000000000000000 : ℝ)*base89 + (27261/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : (0 : ℝ) ≤ ((31003/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31003/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-74177/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-74177/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9329/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9329/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c319086_s0 p hpa hpb X hX

#print axioms solution
