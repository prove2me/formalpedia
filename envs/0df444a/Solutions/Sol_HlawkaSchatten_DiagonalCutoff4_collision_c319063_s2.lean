-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c319063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:31:33.738988+00:00
-- url     : https://prove2.me/submissions/2a79cde3-fcf0-413e-b1bc-4edfb2ad811c

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
theorem collision_support_c319063_s2_s2_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1335968087/10000000000 : ℝ)*x 0 + (5358506219/10000000000 : ℝ)*x 1 + (2690019897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335968087/10000000000 : ℝ)^5 ≤ (8076907422779/100000000000000 : ℝ)^4 := by
    have hnat : (1335968087 : ℕ)^5*100000000000000^4 ≤ 8076907422779^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335968087 10000000000 8076907422779 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5358506219/10000000000 : ℝ)^5 ≤ (11461585079573/25000000000000 : ℝ)^4 := by
    have hnat : (5358506219 : ℕ)^5*25000000000000^4 ≤ 11461585079573^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358506219 10000000000 11461585079573 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2690019897/5000000000 : ℝ)^5 ≤ (9215350450261/20000000000000 : ℝ)^4 := by
    have hnat : (2690019897 : ℕ)^5*20000000000000^4 ≤ 9215350450261^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690019897 5000000000 9215350450261 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1335968087/10000000000 : ℝ), (5358506219/10000000000 : ℝ), (2690019897/5000000000 : ℝ)] ![(8076907422779/100000000000000 : ℝ), (11461585079573/25000000000000 : ℝ), (9215350450261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1335968087/10000000000 : ℝ)|^5 ≤ (8076907422779/100000000000000 : ℝ)^4
        have hw : |(-1335968087/10000000000 : ℝ)|=(1335968087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5358506219/10000000000 : ℝ)|^5 ≤ (11461585079573/25000000000000 : ℝ)^4
        have hw : |(5358506219/10000000000 : ℝ)|=(5358506219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2690019897/5000000000 : ℝ)|^5 ≤ (9215350450261/20000000000000 : ℝ)^4
        have hw : |(2690019897/5000000000 : ℝ)|=(2690019897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (167469797/312500000 : ℝ)*x 0 + (-268087063/2000000000 : ℝ)*x 1 + (2688178957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167469797/312500000 : ℝ)^5 ≤ (22925989786471/50000000000000 : ℝ)^4 := by
    have hnat : (167469797 : ℕ)^5*50000000000000^4 ≤ 22925989786471^4*312500000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167469797 312500000 22925989786471 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268087063/2000000000 : ℝ)^5 ≤ (2027670277719/25000000000000 : ℝ)^4 := by
    have hnat : (268087063 : ℕ)^5*25000000000000^4 ≤ 2027670277719^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268087063 2000000000 2027670277719 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688178957/5000000000 : ℝ)^5 ≤ (46037339309213/100000000000000 : ℝ)^4 := by
    have hnat : (2688178957 : ℕ)^5*100000000000000^4 ≤ 46037339309213^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688178957 5000000000 46037339309213 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167469797/312500000 : ℝ), (-268087063/2000000000 : ℝ), (2688178957/5000000000 : ℝ)] ![(22925989786471/50000000000000 : ℝ), (2027670277719/25000000000000 : ℝ), (46037339309213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167469797/312500000 : ℝ)|^5 ≤ (22925989786471/50000000000000 : ℝ)^4
        have hw : |(167469797/312500000 : ℝ)|=(167469797/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-268087063/2000000000 : ℝ)|^5 ≤ (2027670277719/25000000000000 : ℝ)^4
        have hw : |(-268087063/2000000000 : ℝ)|=(268087063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688178957/5000000000 : ℝ)|^5 ≤ (46037339309213/100000000000000 : ℝ)^4
        have hw : |(2688178957/5000000000 : ℝ)|=(2688178957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5375411451/10000000000 : ℝ)*x 0 + (335820053/625000000 : ℝ)*x 1 + (-330453929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375411451/10000000000 : ℝ)^5 ≤ (23013604459903/50000000000000 : ℝ)^4 := by
    have hnat : (5375411451 : ℕ)^5*50000000000000^4 ≤ 23013604459903^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375411451 10000000000 23013604459903 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335820053/625000000 : ℝ)^5 ≤ (23001346741659/50000000000000 : ℝ)^4 := by
    have hnat : (335820053 : ℕ)^5*50000000000000^4 ≤ 23001346741659^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335820053 625000000 23001346741659 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330453929/2500000000 : ℝ)^5 ≤ (63760780697/800000000000 : ℝ)^4 := by
    have hnat : (330453929 : ℕ)^5*800000000000^4 ≤ 63760780697^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330453929 2500000000 63760780697 800000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375411451/10000000000 : ℝ), (335820053/625000000 : ℝ), (-330453929/2500000000 : ℝ)] ![(23013604459903/50000000000000 : ℝ), (23001346741659/50000000000000 : ℝ), (63760780697/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375411451/10000000000 : ℝ)|^5 ≤ (23013604459903/50000000000000 : ℝ)^4
        have hw : |(5375411451/10000000000 : ℝ)|=(5375411451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(335820053/625000000 : ℝ)|^5 ≤ (23001346741659/50000000000000 : ℝ)^4
        have hw : |(335820053/625000000 : ℝ)|=(335820053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-330453929/2500000000 : ℝ)|^5 ≤ (63760780697/800000000000 : ℝ)^4
        have hw : |(-330453929/2500000000 : ℝ)|=(330453929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2080500829/5000000000 : ℝ)*x 0 + (1039127647/2500000000 : ℝ)*x 1 + (517473703/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080500829/5000000000 : ℝ)^5 ≤ (6683860186597/20000000000000 : ℝ)^4 := by
    have hnat : (2080500829 : ℕ)^5*20000000000000^4 ≤ 6683860186597^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080500829 5000000000 6683860186597 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039127647/2500000000 : ℝ)^5 ≤ (33374219190219/100000000000000 : ℝ)^4 := by
    have hnat : (1039127647 : ℕ)^5*100000000000000^4 ≤ 33374219190219^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039127647 2500000000 33374219190219 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517473703/1250000000 : ℝ)^5 ≤ (33206479867321/100000000000000 : ℝ)^4 := by
    have hnat : (517473703 : ℕ)^5*100000000000000^4 ≤ 33206479867321^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517473703 1250000000 33206479867321 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2080500829/5000000000 : ℝ), (1039127647/2500000000 : ℝ), (517473703/1250000000 : ℝ)] ![(6683860186597/20000000000000 : ℝ), (33374219190219/100000000000000 : ℝ), (33206479867321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2080500829/5000000000 : ℝ)|^5 ≤ (6683860186597/20000000000000 : ℝ)^4
        have hw : |(2080500829/5000000000 : ℝ)|=(2080500829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039127647/2500000000 : ℝ)|^5 ≤ (33374219190219/100000000000000 : ℝ)^4
        have hw : |(1039127647/2500000000 : ℝ)|=(1039127647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517473703/1250000000 : ℝ)|^5 ≤ (33206479867321/100000000000000 : ℝ)^4
        have hw : |(517473703/1250000000 : ℝ)|=(517473703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-15500617/125000000 : ℝ)*x 0 + (1164959081/2500000000 : ℝ)*x 1 + (3060495383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15500617/125000000 : ℝ)^5 ≤ (3679329817481/50000000000000 : ℝ)^4 := by
    have hnat : (15500617 : ℕ)^5*50000000000000^4 ≤ 3679329817481^4*125000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15500617 125000000 3679329817481 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1164959081/2500000000 : ℝ)^5 ≤ (240626439747/625000000000 : ℝ)^4 := by
    have hnat : (1164959081 : ℕ)^5*625000000000^4 ≤ 240626439747^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164959081 2500000000 240626439747 625000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3060495383/5000000000 : ℝ)^5 ≤ (6767638749877/12500000000000 : ℝ)^4 := by
    have hnat : (3060495383 : ℕ)^5*12500000000000^4 ≤ 6767638749877^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3060495383 5000000000 6767638749877 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15500617/125000000 : ℝ), (1164959081/2500000000 : ℝ), (3060495383/5000000000 : ℝ)] ![(3679329817481/50000000000000 : ℝ), (240626439747/625000000000 : ℝ), (6767638749877/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15500617/125000000 : ℝ)|^5 ≤ (3679329817481/50000000000000 : ℝ)^4
        have hw : |(-15500617/125000000 : ℝ)|=(15500617/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1164959081/2500000000 : ℝ)|^5 ≤ (240626439747/625000000000 : ℝ)^4
        have hw : |(1164959081/2500000000 : ℝ)|=(1164959081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3060495383/5000000000 : ℝ)|^5 ≤ (6767638749877/12500000000000 : ℝ)^4
        have hw : |(3060495383/5000000000 : ℝ)|=(3060495383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5049010157/10000000000 : ℝ)*x 0 + (-659064567/10000000000 : ℝ)*x 1 + (6117277629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5049010157/10000000000 : ℝ)^5 ≤ (1330018944871/3125000000000 : ℝ)^4 := by
    have hnat : (5049010157 : ℕ)^5*3125000000000^4 ≤ 1330018944871^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049010157 10000000000 1330018944871 3125000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659064567/10000000000 : ℝ)^5 ≤ (1669667365301/50000000000000 : ℝ)^4 := by
    have hnat : (659064567 : ℕ)^5*50000000000000^4 ≤ 1669667365301^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659064567 10000000000 1669667365301 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6117277629/10000000000 : ℝ)^5 ≤ (6762507377967/12500000000000 : ℝ)^4 := by
    have hnat : (6117277629 : ℕ)^5*12500000000000^4 ≤ 6762507377967^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6117277629 10000000000 6762507377967 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5049010157/10000000000 : ℝ), (-659064567/10000000000 : ℝ), (6117277629/10000000000 : ℝ)] ![(1330018944871/3125000000000 : ℝ), (1669667365301/50000000000000 : ℝ), (6762507377967/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5049010157/10000000000 : ℝ)|^5 ≤ (1330018944871/3125000000000 : ℝ)^4
        have hw : |(5049010157/10000000000 : ℝ)|=(5049010157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-659064567/10000000000 : ℝ)|^5 ≤ (1669667365301/50000000000000 : ℝ)^4
        have hw : |(-659064567/10000000000 : ℝ)|=(659064567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6117277629/10000000000 : ℝ)|^5 ≤ (6762507377967/12500000000000 : ℝ)^4
        have hw : |(6117277629/10000000000 : ℝ)|=(6117277629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4840566559/10000000000 : ℝ)*x 0 + (98904349/156250000 : ℝ)*x 1 + (-631208369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4840566559/10000000000 : ℝ)^5 ≤ (40375716767821/100000000000000 : ℝ)^4 := by
    have hnat : (4840566559 : ℕ)^5*100000000000000^4 ≤ 40375716767821^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4840566559 10000000000 40375716767821 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98904349/156250000 : ℝ)^5 ≤ (7057554107293/12500000000000 : ℝ)^4 := by
    have hnat : (98904349 : ℕ)^5*12500000000000^4 ≤ 7057554107293^4*156250000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98904349 156250000 7057554107293 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (631208369/10000000000 : ℝ)^5 ≤ (3163850366927/100000000000000 : ℝ)^4 := by
    have hnat : (631208369 : ℕ)^5*100000000000000^4 ≤ 3163850366927^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631208369 10000000000 3163850366927 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4840566559/10000000000 : ℝ), (98904349/156250000 : ℝ), (-631208369/10000000000 : ℝ)] ![(40375716767821/100000000000000 : ℝ), (7057554107293/12500000000000 : ℝ), (3163850366927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4840566559/10000000000 : ℝ)|^5 ≤ (40375716767821/100000000000000 : ℝ)^4
        have hw : |(4840566559/10000000000 : ℝ)|=(4840566559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(98904349/156250000 : ℝ)|^5 ≤ (7057554107293/12500000000000 : ℝ)^4
        have hw : |(98904349/156250000 : ℝ)|=(98904349/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-631208369/10000000000 : ℝ)|^5 ≤ (3163850366927/100000000000000 : ℝ)^4
        have hw : |(-631208369/10000000000 : ℝ)|=(631208369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1120630927/2500000000 : ℝ)*x 0 + (554519831/1000000000 : ℝ)*x 1 + (2247015481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120630927/2500000000 : ℝ)^5 ≤ (36677797128707/100000000000000 : ℝ)^4 := by
    have hnat : (1120630927 : ℕ)^5*100000000000000^4 ≤ 36677797128707^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120630927 2500000000 36677797128707 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554519831/1000000000 : ℝ)^5 ≤ (23925793886277/50000000000000 : ℝ)^4 := by
    have hnat : (554519831 : ℕ)^5*50000000000000^4 ≤ 23925793886277^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554519831 1000000000 23925793886277 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247015481/10000000000 : ℝ)^5 ≤ (7735307539451/50000000000000 : ℝ)^4 := by
    have hnat : (2247015481 : ℕ)^5*50000000000000^4 ≤ 7735307539451^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247015481 10000000000 7735307539451 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120630927/2500000000 : ℝ), (554519831/1000000000 : ℝ), (2247015481/10000000000 : ℝ)] ![(36677797128707/100000000000000 : ℝ), (23925793886277/50000000000000 : ℝ), (7735307539451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120630927/2500000000 : ℝ)|^5 ≤ (36677797128707/100000000000000 : ℝ)^4
        have hw : |(1120630927/2500000000 : ℝ)|=(1120630927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554519831/1000000000 : ℝ)|^5 ≤ (23925793886277/50000000000000 : ℝ)^4
        have hw : |(554519831/1000000000 : ℝ)|=(554519831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247015481/10000000000 : ℝ)|^5 ≤ (7735307539451/50000000000000 : ℝ)^4
        have hw : |(2247015481/10000000000 : ℝ)|=(2247015481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-657641779/10000000000 : ℝ)*x 0 + (2528952101/5000000000 : ℝ)*x 1 + (1527403027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657641779/10000000000 : ℝ)^5 ≤ (3330325972533/100000000000000 : ℝ)^4 := by
    have hnat : (657641779 : ℕ)^5*100000000000000^4 ≤ 3330325972533^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657641779 10000000000 3330325972533 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2528952101/5000000000 : ℝ)^5 ≤ (42654342247863/100000000000000 : ℝ)^4 := by
    have hnat : (2528952101 : ℕ)^5*100000000000000^4 ≤ 42654342247863^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528952101 5000000000 42654342247863 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1527403027/2500000000 : ℝ)^5 ≤ (13503832939789/25000000000000 : ℝ)^4 := by
    have hnat : (1527403027 : ℕ)^5*25000000000000^4 ≤ 13503832939789^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1527403027 2500000000 13503832939789 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-657641779/10000000000 : ℝ), (2528952101/5000000000 : ℝ), (1527403027/2500000000 : ℝ)] ![(3330325972533/100000000000000 : ℝ), (42654342247863/100000000000000 : ℝ), (13503832939789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-657641779/10000000000 : ℝ)|^5 ≤ (3330325972533/100000000000000 : ℝ)^4
        have hw : |(-657641779/10000000000 : ℝ)|=(657641779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2528952101/5000000000 : ℝ)|^5 ≤ (42654342247863/100000000000000 : ℝ)^4
        have hw : |(2528952101/5000000000 : ℝ)|=(2528952101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1527403027/2500000000 : ℝ)|^5 ≤ (13503832939789/25000000000000 : ℝ)^4
        have hw : |(1527403027/2500000000 : ℝ)|=(1527403027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2339633427/5000000000 : ℝ)*x 0 + (-1235468113/10000000000 : ℝ)*x 1 + (1526474743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2339633427/5000000000 : ℝ)^5 ≤ (7740201419649/20000000000000 : ℝ)^4 := by
    have hnat : (2339633427 : ℕ)^5*20000000000000^4 ≤ 7740201419649^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2339633427 5000000000 7740201419649 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1235468113/10000000000 : ℝ)^5 ≤ (1464938597649/20000000000000 : ℝ)^4 := by
    have hnat : (1235468113 : ℕ)^5*20000000000000^4 ≤ 1464938597649^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235468113 10000000000 1464938597649 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1526474743/2500000000 : ℝ)^5 ≤ (10794859978407/20000000000000 : ℝ)^4 := by
    have hnat : (1526474743 : ℕ)^5*20000000000000^4 ≤ 10794859978407^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526474743 2500000000 10794859978407 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2339633427/5000000000 : ℝ), (-1235468113/10000000000 : ℝ), (1526474743/2500000000 : ℝ)] ![(7740201419649/20000000000000 : ℝ), (1464938597649/20000000000000 : ℝ), (10794859978407/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2339633427/5000000000 : ℝ)|^5 ≤ (7740201419649/20000000000000 : ℝ)^4
        have hw : |(2339633427/5000000000 : ℝ)|=(2339633427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1235468113/10000000000 : ℝ)|^5 ≤ (1464938597649/20000000000000 : ℝ)^4
        have hw : |(-1235468113/10000000000 : ℝ)|=(1235468113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1526474743/2500000000 : ℝ)|^5 ≤ (10794859978407/20000000000000 : ℝ)^4
        have hw : |(1526474743/2500000000 : ℝ)|=(1526474743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3052079021/5000000000 : ℝ)*x 0 + (5072630047/10000000000 : ℝ)*x 1 + (-321293663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3052079021/5000000000 : ℝ)^5 ≤ (53955063959467/100000000000000 : ℝ)^4 := by
    have hnat : (3052079021 : ℕ)^5*100000000000000^4 ≤ 53955063959467^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3052079021 5000000000 53955063959467 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5072630047/10000000000 : ℝ)^5 ≤ (42809631285167/100000000000000 : ℝ)^4 := by
    have hnat : (5072630047 : ℕ)^5*100000000000000^4 ≤ 42809631285167^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072630047 10000000000 42809631285167 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321293663/5000000000 : ℝ)^5 ≤ (3235304743019/100000000000000 : ℝ)^4 := by
    have hnat : (321293663 : ℕ)^5*100000000000000^4 ≤ 3235304743019^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321293663 5000000000 3235304743019 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3052079021/5000000000 : ℝ), (5072630047/10000000000 : ℝ), (-321293663/5000000000 : ℝ)] ![(53955063959467/100000000000000 : ℝ), (42809631285167/100000000000000 : ℝ), (3235304743019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3052079021/5000000000 : ℝ)|^5 ≤ (53955063959467/100000000000000 : ℝ)^4
        have hw : |(3052079021/5000000000 : ℝ)|=(3052079021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5072630047/10000000000 : ℝ)|^5 ≤ (42809631285167/100000000000000 : ℝ)^4
        have hw : |(5072630047/10000000000 : ℝ)|=(5072630047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-321293663/5000000000 : ℝ)|^5 ≤ (3235304743019/100000000000000 : ℝ)^4
        have hw : |(-321293663/5000000000 : ℝ)|=(321293663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3053205699/5000000000 : ℝ)*x 0 + (3845695849/10000000000 : ℝ)*x 1 + (1138879983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3053205699/5000000000 : ℝ)^5 ≤ (13494990516243/25000000000000 : ℝ)^4 := by
    have hnat : (3053205699 : ℕ)^5*25000000000000^4 ≤ 13494990516243^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3053205699 5000000000 13494990516243 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3845695849/10000000000 : ℝ)^5 ≤ (15142189299269/50000000000000 : ℝ)^4 := by
    have hnat : (3845695849 : ℕ)^5*50000000000000^4 ≤ 15142189299269^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3845695849 10000000000 15142189299269 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1138879983/5000000000 : ℝ)^5 ≤ (3933914829329/25000000000000 : ℝ)^4 := by
    have hnat : (1138879983 : ℕ)^5*25000000000000^4 ≤ 3933914829329^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138879983 5000000000 3933914829329 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3053205699/5000000000 : ℝ), (3845695849/10000000000 : ℝ), (1138879983/5000000000 : ℝ)] ![(13494990516243/25000000000000 : ℝ), (15142189299269/50000000000000 : ℝ), (3933914829329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3053205699/5000000000 : ℝ)|^5 ≤ (13494990516243/25000000000000 : ℝ)^4
        have hw : |(3053205699/5000000000 : ℝ)|=(3053205699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3845695849/10000000000 : ℝ)|^5 ≤ (15142189299269/50000000000000 : ℝ)^4
        have hw : |(3845695849/10000000000 : ℝ)|=(3845695849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1138879983/5000000000 : ℝ)|^5 ≤ (3933914829329/25000000000000 : ℝ)^4
        have hw : |(1138879983/5000000000 : ℝ)|=(1138879983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-60246537/1000000000 : ℝ)*x 0 + (5806421989/10000000000 : ℝ)*x 1 + (337727057/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60246537/1000000000 : ℝ)^5 ≤ (2984799138173/100000000000000 : ℝ)^4 := by
    have hnat : (60246537 : ℕ)^5*100000000000000^4 ≤ 2984799138173^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60246537 1000000000 2984799138173 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5806421989/10000000000 : ℝ)^5 ≤ (25342867254341/50000000000000 : ℝ)^4 := by
    have hnat : (5806421989 : ℕ)^5*50000000000000^4 ≤ 25342867254341^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5806421989 10000000000 25342867254341 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337727057/625000000 : ℝ)^5 ≤ (5791183293167/12500000000000 : ℝ)^4 := by
    have hnat : (337727057 : ℕ)^5*12500000000000^4 ≤ 5791183293167^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337727057 625000000 5791183293167 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-60246537/1000000000 : ℝ), (5806421989/10000000000 : ℝ), (337727057/625000000 : ℝ)] ![(2984799138173/100000000000000 : ℝ), (25342867254341/50000000000000 : ℝ), (5791183293167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-60246537/1000000000 : ℝ)|^5 ≤ (2984799138173/100000000000000 : ℝ)^4
        have hw : |(-60246537/1000000000 : ℝ)|=(60246537/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5806421989/10000000000 : ℝ)|^5 ≤ (25342867254341/50000000000000 : ℝ)^4
        have hw : |(5806421989/10000000000 : ℝ)|=(5806421989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337727057/625000000 : ℝ)|^5 ≤ (5791183293167/12500000000000 : ℝ)^4
        have hw : |(337727057/625000000 : ℝ)|=(337727057/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (6142825143/10000000000 : ℝ)*x 0 + (-600131453/10000000000 : ℝ)*x 1 + (1264302381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6142825143/10000000000 : ℝ)^5 ≤ (54382628097903/100000000000000 : ℝ)^4 := by
    have hnat : (6142825143 : ℕ)^5*100000000000000^4 ≤ 54382628097903^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6142825143 10000000000 54382628097903 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600131453/10000000000 : ℝ)^5 ≤ (1485176231909/50000000000000 : ℝ)^4 := by
    have hnat : (600131453 : ℕ)^5*50000000000000^4 ≤ 1485176231909^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600131453 10000000000 1485176231909 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1264302381/2500000000 : ℝ)^5 ≤ (1066175485531/2500000000000 : ℝ)^4 := by
    have hnat : (1264302381 : ℕ)^5*2500000000000^4 ≤ 1066175485531^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264302381 2500000000 1066175485531 2500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6142825143/10000000000 : ℝ), (-600131453/10000000000 : ℝ), (1264302381/2500000000 : ℝ)] ![(54382628097903/100000000000000 : ℝ), (1485176231909/50000000000000 : ℝ), (1066175485531/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6142825143/10000000000 : ℝ)|^5 ≤ (54382628097903/100000000000000 : ℝ)^4
        have hw : |(6142825143/10000000000 : ℝ)|=(6142825143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-600131453/10000000000 : ℝ)|^5 ≤ (1485176231909/50000000000000 : ℝ)^4
        have hw : |(-600131453/10000000000 : ℝ)|=(600131453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1264302381/2500000000 : ℝ)|^5 ≤ (1066175485531/2500000000000 : ℝ)^4
        have hw : |(1264302381/2500000000 : ℝ)|=(1264302381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2314950801/5000000000 : ℝ)*x 0 + (6163857643/10000000000 : ℝ)*x 1 + (-608846207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2314950801/5000000000 : ℝ)^5 ≤ (7638264569731/20000000000000 : ℝ)^4 := by
    have hnat : (2314950801 : ℕ)^5*20000000000000^4 ≤ 7638264569731^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314950801 5000000000 7638264569731 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6163857643/10000000000 : ℝ)^5 ≤ (10923095874941/20000000000000 : ℝ)^4 := by
    have hnat : (6163857643 : ℕ)^5*20000000000000^4 ≤ 10923095874941^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6163857643 10000000000 10923095874941 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (608846207/5000000000 : ℝ)^5 ≤ (449574860229/6250000000000 : ℝ)^4 := by
    have hnat : (608846207 : ℕ)^5*6250000000000^4 ≤ 449574860229^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608846207 5000000000 449574860229 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2314950801/5000000000 : ℝ), (6163857643/10000000000 : ℝ), (-608846207/5000000000 : ℝ)] ![(7638264569731/20000000000000 : ℝ), (10923095874941/20000000000000 : ℝ), (449574860229/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2314950801/5000000000 : ℝ)|^5 ≤ (7638264569731/20000000000000 : ℝ)^4
        have hw : |(2314950801/5000000000 : ℝ)|=(2314950801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6163857643/10000000000 : ℝ)|^5 ≤ (10923095874941/20000000000000 : ℝ)^4
        have hw : |(6163857643/10000000000 : ℝ)|=(6163857643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-608846207/5000000000 : ℝ)|^5 ≤ (449574860229/6250000000000 : ℝ)^4
        have hw : |(-608846207/5000000000 : ℝ)|=(608846207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319063_s2_s2_27 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3142199387/5000000000 : ℝ)*x 0 + (95470413/312500000 : ℝ)*x 1 + (581132949/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3142199387/5000000000 : ℝ)^5 ≤ (55953810674111/100000000000000 : ℝ)^4 := by
    have hnat : (3142199387 : ℕ)^5*100000000000000^4 ≤ 55953810674111^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3142199387 5000000000 55953810674111 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95470413/312500000 : ℝ)^5 ≤ (5678236580533/25000000000000 : ℝ)^4 := by
    have hnat : (95470413 : ℕ)^5*25000000000000^4 ≤ 5678236580533^4*312500000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95470413 312500000 5678236580533 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (581132949/2000000000 : ℝ)^5 ≤ (21333242988269/100000000000000 : ℝ)^4 := by
    have hnat : (581132949 : ℕ)^5*100000000000000^4 ≤ 21333242988269^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581132949 2000000000 21333242988269 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3142199387/5000000000 : ℝ), (95470413/312500000 : ℝ), (581132949/2000000000 : ℝ)] ![(55953810674111/100000000000000 : ℝ), (5678236580533/25000000000000 : ℝ), (21333242988269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3142199387/5000000000 : ℝ)|^5 ≤ (55953810674111/100000000000000 : ℝ)^4
        have hw : |(3142199387/5000000000 : ℝ)|=(3142199387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(95470413/312500000 : ℝ)|^5 ≤ (5678236580533/25000000000000 : ℝ)^4
        have hw : |(95470413/312500000 : ℝ)|=(95470413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(581132949/2000000000 : ℝ)|^5 ≤ (21333242988269/100000000000000 : ℝ)^4
        have hw : |(581132949/2000000000 : ℝ)|=(581132949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319063_s2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((51641/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(51641/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26079/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(26079/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12477/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12477/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31897/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31897/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32371/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32371/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6193/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6193/20000 : ℝ)*X 1 2) := by
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
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (51641/100000 : ℝ) ^ (79/16 : ℝ) ≤ (1913731726798855711/50000000000000000000 : ℝ) := by
    have hpowers : (51641/100000 : ℝ)^79 ≤ (1913731726798855711/50000000000000000000 : ℝ)^16 := by
      have hnat : (51641 : ℕ)^79*50000000000000000000^16 ≤ 1913731726798855711^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51641 100000 1913731726798855711 50000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (51641/100000 : ℝ)) (X := (1913731726798855711/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (51913731726798855711/50000000000000000000 : ℝ) ≤ (5038180817027197/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (51913731726798855711/50000000000000000000 : ℝ)^16 ≤ (5038180817027197/5000000000000000 : ℝ)^79 := by
      have hnat : (51913731726798855711 : ℕ)^16*5000000000000000^79 ≤ 5038180817027197^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51913731726798855711 50000000000000000000 5038180817027197 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5038180817027197/5000000000000000 : ℝ)) (X := (51913731726798855711/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (26913731726798855711/25000000000000000000 : ℝ) ≤ (1015051040194877/1000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (26913731726798855711/25000000000000000000 : ℝ)^16 ≤ (1015051040194877/1000000000000000 : ℝ)^79 := by
      have hnat : (26913731726798855711 : ℕ)^16*1000000000000000^79 ≤ 1015051040194877^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26913731726798855711 25000000000000000000 1015051040194877 1000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1015051040194877/1000000000000000 : ℝ)) (X := (26913731726798855711/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(38180817027197/2582050000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(9268595986797/645512500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (51641/100000 : ℝ)) (alpha := (38180817027197/2582050000000000 : ℝ)) (beta := (9268595986797/645512500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (51641/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(38180817027197/2582050000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(9268595986797/645512500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (26079/50000 : ℝ) ^ (79/16 : ℝ) ≤ (160817047043504507/4000000000000000000 : ℝ) := by
    have hpowers : (26079/50000 : ℝ)^79 ≤ (160817047043504507/4000000000000000000 : ℝ)^16 := by
      have hnat : (26079 : ℕ)^79*4000000000000000000^16 ≤ 160817047043504507^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26079 50000 160817047043504507 4000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26079/50000 : ℝ)) (X := (160817047043504507/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (4160817047043504507/4000000000000000000 : ℝ) ≤ (201603032158857/200000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (4160817047043504507/4000000000000000000 : ℝ)^16 ≤ (201603032158857/200000000000000 : ℝ)^79 := by
      have hnat : (4160817047043504507 : ℕ)^16*200000000000000^79 ≤ 201603032158857^79*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4160817047043504507 4000000000000000000 201603032158857 200000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (201603032158857/200000000000000 : ℝ)) (X := (4160817047043504507/4000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (2160817047043504507/2000000000000000000 : ℝ) ≤ (2031573919636463/2000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2160817047043504507/2000000000000000000 : ℝ)^16 ≤ (2031573919636463/2000000000000000 : ℝ)^79 := by
      have hnat : (2160817047043504507 : ℕ)^16*2000000000000000^79 ≤ 2031573919636463^79*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2160817047043504507 2000000000000000000 2031573919636463 2000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2031573919636463/2000000000000000 : ℝ)) (X := (2160817047043504507/2000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1603032158857/104316000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(15543598047893/1043160000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (26079/50000 : ℝ)) (alpha := (1603032158857/104316000000000 : ℝ)) (beta := (15543598047893/1043160000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (26079/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1603032158857/104316000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(15543598047893/1043160000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (12477/25000 : ℝ) ^ (79/16 : ℝ) ≤ (323381518978570193/10000000000000000000 : ℝ) := by
    have hpowers : (12477/25000 : ℝ)^79 ≤ (323381518978570193/10000000000000000000 : ℝ)^16 := by
      have hnat : (12477 : ℕ)^79*10000000000000000000^16 ≤ 323381518978570193^16*25000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12477 25000 323381518978570193 10000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12477/25000 : ℝ)) (X := (323381518978570193/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (10323381518978570193/10000000000000000000 : ℝ) ≤ (10064666479146617/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (10323381518978570193/10000000000000000000 : ℝ)^16 ≤ (10064666479146617/10000000000000000 : ℝ)^79 := by
      have hnat : (10323381518978570193 : ℕ)^16*10000000000000000^79 ≤ 10064666479146617^79*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10323381518978570193 10000000000000000000 10064666479146617 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10064666479146617/10000000000000000 : ℝ)) (X := (10323381518978570193/10000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (5323381518978570193/5000000000000000000 : ℝ) ≤ (5063868593187937/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (5323381518978570193/5000000000000000000 : ℝ)^16 ≤ (5063868593187937/5000000000000000 : ℝ)^79 := by
      have hnat : (5323381518978570193 : ℕ)^16*5000000000000000^79 ≤ 5063868593187937^79*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5323381518978570193 5000000000000000000 5063868593187937 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5063868593187937/5000000000000000 : ℝ)) (X := (5323381518978570193/5000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(64666479146617/4990800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(21023569076419/1663600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (12477/25000 : ℝ)) (alpha := (64666479146617/4990800000000000 : ℝ)) (beta := (21023569076419/1663600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (12477/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(64666479146617/4990800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(21023569076419/1663600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1335968087/10000000000 : ℝ)*X 0 0+(5358506219/10000000000 : ℝ)*X 0 1+(2690019897/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((167469797/312500000 : ℝ)*X 1 0+(-268087063/2000000000 : ℝ)*X 1 1+(2688178957/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5375411451/10000000000 : ℝ)*X 2 0+(335820053/625000000 : ℝ)*X 2 1+(-330453929/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((2080500829/5000000000 : ℝ)*X 0 0+(1039127647/2500000000 : ℝ)*X 0 1+(517473703/1250000000 : ℝ)*X 0 2+(2080500829/5000000000 : ℝ)*X 1 0+(1039127647/2500000000 : ℝ)*X 1 1+(517473703/1250000000 : ℝ)*X 1 2+(2080500829/5000000000 : ℝ)*X 2 0+(1039127647/2500000000 : ℝ)*X 2 1+(517473703/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-15500617/125000000 : ℝ)*X 0 0+(1164959081/2500000000 : ℝ)*X 0 1+(3060495383/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((5049010157/10000000000 : ℝ)*X 1 0+(-659064567/10000000000 : ℝ)*X 1 1+(6117277629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4840566559/10000000000 : ℝ)*X 2 0+(98904349/156250000 : ℝ)*X 2 1+(-631208369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1120630927/2500000000 : ℝ)*X 0 0+(554519831/1000000000 : ℝ)*X 0 1+(2247015481/10000000000 : ℝ)*X 0 2+(1120630927/2500000000 : ℝ)*X 1 0+(554519831/1000000000 : ℝ)*X 1 1+(2247015481/10000000000 : ℝ)*X 1 2+(1120630927/2500000000 : ℝ)*X 2 0+(554519831/1000000000 : ℝ)*X 2 1+(2247015481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-657641779/10000000000 : ℝ)*X 0 0+(2528952101/5000000000 : ℝ)*X 0 1+(1527403027/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2339633427/5000000000 : ℝ)*X 1 0+(-1235468113/10000000000 : ℝ)*X 1 1+(1526474743/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3052079021/5000000000 : ℝ)*X 2 0+(5072630047/10000000000 : ℝ)*X 2 1+(-321293663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3053205699/5000000000 : ℝ)*X 0 0+(3845695849/10000000000 : ℝ)*X 0 1+(1138879983/5000000000 : ℝ)*X 0 2+(3053205699/5000000000 : ℝ)*X 1 0+(3845695849/10000000000 : ℝ)*X 1 1+(1138879983/5000000000 : ℝ)*X 1 2+(3053205699/5000000000 : ℝ)*X 2 0+(3845695849/10000000000 : ℝ)*X 2 1+(1138879983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-60246537/1000000000 : ℝ)*X 0 0+(5806421989/10000000000 : ℝ)*X 0 1+(337727057/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((6142825143/10000000000 : ℝ)*X 1 0+(-600131453/10000000000 : ℝ)*X 1 1+(1264302381/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2314950801/5000000000 : ℝ)*X 2 0+(6163857643/10000000000 : ℝ)*X 2 1+(-608846207/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3142199387/5000000000 : ℝ)*X 0 0+(95470413/312500000 : ℝ)*X 0 1+(581132949/2000000000 : ℝ)*X 0 2+(3142199387/5000000000 : ℝ)*X 1 0+(95470413/312500000 : ℝ)*X 1 1+(581132949/2000000000 : ℝ)*X 1 2+(3142199387/5000000000 : ℝ)*X 2 0+(95470413/312500000 : ℝ)*X 2 1+(581132949/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((31897/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31897/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1241596544678449572582151327749/93351918543350000000000000000000000 : ℝ) := by norm_num
    linear_combination (426293/250000000000 : ℝ)*(base50) + (157271153433/1000000000000 : ℝ)*(base60) + (4789417438863/1000000000000 : ℝ)*(major_s2_0) + (4789417438863/1000000000000 : ℝ)*(major_s2_1) + (4789417438863/1000000000000 : ℝ)*(major_s2_2) + (12611/488281250 : ℝ)*(sp_s2_0) + (17301443/1000000000000 : ℝ)*(sp_s2_6) + (873900137763/125000000000 : ℝ)*(sp_s2_7) + (43694903437/6250000000 : ℝ)*(sp_s2_8) + (6991182660727/1000000000000 : ℝ)*(sp_s2_9) + (2587542229857/1000000000000 : ℝ)*(sp_s2_13) + (43983599/1000000000000 : ℝ)*(sp_s2_14) + (86363111/1000000000000 : ℝ)*(sp_s2_15) + (5515769/62500000000 : ℝ)*(sp_s2_23) + (2587559531299/1000000000000 : ℝ)*(f.failure) + (6991270913031/1000000000000 : ℝ)*(f.sum) + (4660383796861631339/14461674800000000000000000000000 : ℝ)*base62 + (45175384813203/1663600000000000000000000000 : ℝ)*base64 + (136038624090811/347720000000000000000000000 : ℝ)*base66 + (840225733646083/1663600000000000000000000000 : ℝ)*base68 + (8606095628295643291/85909967600000000000000000000000 : ℝ)*base70 + (300104189321061/2582050000000000000000000000 : ℝ)*base72 + (5303298101699/173860000000000000000000000 : ℝ)*base75 + (637616891856079/2582050000000000000000000000 : ℝ)*base76 + (49449308881095042067/89783042600000000000000000000000 : ℝ)*base78 + (21447/50000000000000000 : ℝ)*base86 + (21447/50000000000000000 : ℝ)*base88 + (21447/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32371/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32371/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3157443773260214867843050411903/186703837086700000000000000000000000 : ℝ) := by norm_num
    linear_combination (4206193/1000000000000 : ℝ)*(base60) + (4864180926869/1000000000000 : ℝ)*(major_s2_0) + (4864180926869/1000000000000 : ℝ)*(major_s2_1) + (4864180926869/1000000000000 : ℝ)*(major_s2_2) + (40864147/1000000000000 : ℝ)*(sp_s2_0) + (19300251/500000000000 : ℝ)*(sp_s2_1) + (98951993/1000000000000 : ℝ)*(sp_s2_2) + (67051301/1000000000000 : ℝ)*(sp_s2_7) + (12774913/200000000000 : ℝ)*(sp_s2_8) + (3550148298591/500000000000 : ℝ)*(sp_s2_14) + (1775075509391/250000000000 : ℝ)*(sp_s2_15) + (3550152780319/500000000000 : ℝ)*(sp_s2_16) + (656962173261/250000000000 : ℝ)*(sp_s2_20) + (20602177/200000000000 : ℝ)*(sp_s2_27) + (2627951703929/1000000000000 : ℝ)*(f.failure) + (7100404512631/1000000000000 : ℝ)*(f.sum) + (12270944295909056137/14461674800000000000000000000000 : ℝ)*base62 + (310200110181191/1663600000000000000000000000 : ℝ)*base65 + (234139047293987/1043160000000000000000000000 : ℝ)*base66 + (7040503787866507/4990800000000000000000000000 : ℝ)*base68 + (28116363260983116407/85909967600000000000000000000000 : ℝ)*base71 + (1094549907300939/1291025000000000000000000000 : ℝ)*base72 + (497765517304613/521580000000000000000000000 : ℝ)*base74 + (2141717793937837/2582050000000000000000000000 : ℝ)*base76 + (24137626169170637303/269349127800000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (67163/50000000000000000 : ℝ)*base87 + (67163/50000000000000000 : ℝ)*base89 + (67163/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6193/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6193/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (95410057037359033124888043/22445760650000000000000000000000 : ℝ) := by norm_num
    linear_combination (468607/200000000000 : ℝ)*(base15) + (7002423483/31250000000 : ℝ)*(base40) + (2239580579559/500000000000 : ℝ)*(major_s2_0) + (2239580579559/500000000000 : ℝ)*(major_s2_1) + (2239580579559/500000000000 : ℝ)*(major_s2_2) + (3015313/125000000000 : ℝ)*(sp_s2_0) + (24794221/1000000000000 : ℝ)*(sp_s2_1) + (5010823/1000000000000 : ℝ)*(sp_s2_2) + (1047591/62500000000 : ℝ)*(sp_s2_9) + (3745627/125000000000 : ℝ)*(sp_s2_20) + (204323692973/31250000000 : ℝ)*(sp_s2_21) + (1307671032077/200000000000 : ℝ)*(sp_s2_22) + (81729506567/12500000000 : ℝ)*(sp_s2_23) + (604977159669/250000000000 : ℝ)*(sp_s2_27) + (604984650923/250000000000 : ℝ)*(f.failure) + (163459557441/25000000000 : ℝ)*(f.sum) + (485001990742375733/7230837400000000000000000000000 : ℝ)*base63 + (119529393152821/831800000000000000000000000 : ℝ)*base65 + (5571078996021/34772000000000000000000000 : ℝ)*base67 + (400154304191279/831800000000000000000000000 : ℝ)*base68 + (6274758155640204283/42954983800000000000000000000000 : ℝ)*base70 + (24360741087067/1291025000000000000000000000 : ℝ)*base73 + (3827195098783/5433125000000000000000000 : ℝ)*base75 + (654268716540623/1291025000000000000000000000 : ℝ)*base77 + (7630456480496571949/44891521300000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base84 + (4119/12500000000000000 : ℝ)*base86 + (4119/12500000000000000 : ℝ)*base88 + (4119/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((51641/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(51641/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26079/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(26079/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12477/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12477/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31897/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31897/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32371/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32371/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6193/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6193/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c319063_s2 p hpa hpb X hX hprev1

#print axioms solution
