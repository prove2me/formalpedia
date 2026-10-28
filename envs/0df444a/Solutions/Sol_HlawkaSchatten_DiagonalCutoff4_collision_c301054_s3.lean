-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301054_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:31:38.513994+00:00
-- url     : https://prove2.me/submissions/99927305-18c9-4cd4-b1d8-558f0df7f6a8

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
theorem collision_support_c301054_s3_s3_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5755529209/10000000000 : ℝ)*x 0 + (-531476917/2500000000 : ℝ)*x 1 + (-4928867137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5755529209/10000000000 : ℝ)^65 ≤ (750871779221/1562500000000 : ℝ)^49 := by
    have hnat : (5755529209 : ℕ)^65*1562500000000^49 ≤ 750871779221^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5755529209 10000000000 750871779221 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531476917/2500000000 : ℝ)^65 ≤ (2564466645179/20000000000000 : ℝ)^49 := by
    have hnat : (531476917 : ℕ)^65*20000000000000^49 ≤ 2564466645179^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531476917 2500000000 2564466645179 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4928867137/10000000000 : ℝ)^65 ≤ (19560936441541/50000000000000 : ℝ)^49 := by
    have hnat : (4928867137 : ℕ)^65*50000000000000^49 ≤ 19560936441541^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4928867137 10000000000 19560936441541 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5755529209/10000000000 : ℝ), (-531476917/2500000000 : ℝ), (-4928867137/10000000000 : ℝ)] ![(750871779221/1562500000000 : ℝ), (2564466645179/20000000000000 : ℝ), (19560936441541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5755529209/10000000000 : ℝ)|^65 ≤ (750871779221/1562500000000 : ℝ)^49
        have hw : |(5755529209/10000000000 : ℝ)|=(5755529209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-531476917/2500000000 : ℝ)|^65 ≤ (2564466645179/20000000000000 : ℝ)^49
        have hw : |(-531476917/2500000000 : ℝ)|=(531476917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4928867137/10000000000 : ℝ)|^65 ≤ (19560936441541/50000000000000 : ℝ)^49
        have hw : |(-4928867137/10000000000 : ℝ)|=(4928867137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1380700061/2500000000 : ℝ)*x 0 + (108948901/200000000 : ℝ)*x 1 + (43502527/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380700061/2500000000 : ℝ)^65 ≤ (22747646445071/50000000000000 : ℝ)^49 := by
    have hnat : (1380700061 : ℕ)^65*50000000000000^49 ≤ 22747646445071^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380700061 2500000000 22747646445071 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108948901/200000000 : ℝ)^65 ≤ (44673682212617/100000000000000 : ℝ)^49 := by
    have hnat : (108948901 : ℕ)^65*100000000000000^49 ≤ 44673682212617^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108948901 200000000 44673682212617 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43502527/250000000 : ℝ)^65 ≤ (38402440959/390625000000 : ℝ)^49 := by
    have hnat : (43502527 : ℕ)^65*390625000000^49 ≤ 38402440959^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43502527 250000000 38402440959 390625000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1380700061/2500000000 : ℝ), (108948901/200000000 : ℝ), (43502527/250000000 : ℝ)] ![(22747646445071/50000000000000 : ℝ), (44673682212617/100000000000000 : ℝ), (38402440959/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1380700061/2500000000 : ℝ)|^65 ≤ (22747646445071/50000000000000 : ℝ)^49
        have hw : |(1380700061/2500000000 : ℝ)|=(1380700061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108948901/200000000 : ℝ)|^65 ≤ (44673682212617/100000000000000 : ℝ)^49
        have hw : |(108948901/200000000 : ℝ)|=(108948901/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43502527/250000000 : ℝ)|^65 ≤ (38402440959/390625000000 : ℝ)^49
        have hw : |(43502527/250000000 : ℝ)|=(43502527/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5413611911/10000000000 : ℝ)*x 0 + (334736439/625000000 : ℝ)*x 1 + (-404833129/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413611911/10000000000 : ℝ)^65 ≤ (44305996087041/100000000000000 : ℝ)^49 := by
    have hnat : (5413611911 : ℕ)^65*100000000000000^49 ≤ 44305996087041^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413611911 10000000000 44305996087041 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (334736439/625000000 : ℝ)^65 ≤ (21839635132449/50000000000000 : ℝ)^49 := by
    have hnat : (334736439 : ℕ)^65*50000000000000^49 ≤ 21839635132449^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334736439 625000000 21839635132449 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404833129/2000000000 : ℝ)^65 ≤ (6007366822621/50000000000000 : ℝ)^49 := by
    have hnat : (404833129 : ℕ)^65*50000000000000^49 ≤ 6007366822621^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404833129 2000000000 6007366822621 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413611911/10000000000 : ℝ), (334736439/625000000 : ℝ), (-404833129/2000000000 : ℝ)] ![(44305996087041/100000000000000 : ℝ), (21839635132449/50000000000000 : ℝ), (6007366822621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413611911/10000000000 : ℝ)|^65 ≤ (44305996087041/100000000000000 : ℝ)^49
        have hw : |(5413611911/10000000000 : ℝ)|=(5413611911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(334736439/625000000 : ℝ)|^65 ≤ (21839635132449/50000000000000 : ℝ)^49
        have hw : |(334736439/625000000 : ℝ)|=(334736439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-404833129/2000000000 : ℝ)|^65 ≤ (6007366822621/50000000000000 : ℝ)^49
        have hw : |(-404833129/2000000000 : ℝ)|=(404833129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-165034959/5000000000 : ℝ)*x 0 + (1615733537/5000000000 : ℝ)*x 1 + (-15970877/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165034959/5000000000 : ℝ)^65 ≤ (108364102307/10000000000000 : ℝ)^49 := by
    have hnat : (165034959 : ℕ)^65*10000000000000^49 ≤ 108364102307^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165034959 5000000000 108364102307 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1615733537/5000000000 : ℝ)^65 ≤ (22346202517331/100000000000000 : ℝ)^49 := by
    have hnat : (1615733537 : ℕ)^65*100000000000000^49 ≤ 22346202517331^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615733537 5000000000 22346202517331 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15970877/19531250 : ℝ)^65 ≤ (76570156442783/100000000000000 : ℝ)^49 := by
    have hnat : (15970877 : ℕ)^65*100000000000000^49 ≤ 76570156442783^49*19531250^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15970877 19531250 76570156442783 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-165034959/5000000000 : ℝ), (1615733537/5000000000 : ℝ), (-15970877/19531250 : ℝ)] ![(108364102307/10000000000000 : ℝ), (22346202517331/100000000000000 : ℝ), (76570156442783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-165034959/5000000000 : ℝ)|^65 ≤ (108364102307/10000000000000 : ℝ)^49
        have hw : |(-165034959/5000000000 : ℝ)|=(165034959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1615733537/5000000000 : ℝ)|^65 ≤ (22346202517331/100000000000000 : ℝ)^49
        have hw : |(1615733537/5000000000 : ℝ)|=(1615733537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15970877/19531250 : ℝ)|^65 ≤ (76570156442783/100000000000000 : ℝ)^49
        have hw : |(-15970877/19531250 : ℝ)|=(15970877/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (118920389/250000000 : ℝ)*x 0 + (-246777689/2500000000 : ℝ)*x 1 + (-6636118299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118920389/250000000 : ℝ)^65 ≤ (18660368454637/50000000000000 : ℝ)^49 := by
    have hnat : (118920389 : ℕ)^65*50000000000000^49 ≤ 18660368454637^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118920389 250000000 18660368454637 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246777689/2500000000 : ℝ)^65 ≤ (4634421824407/100000000000000 : ℝ)^49 := by
    have hnat : (246777689 : ℕ)^65*100000000000000^49 ≤ 4634421824407^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246777689 2500000000 4634421824407 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6636118299/10000000000 : ℝ)^65 ≤ (14511210312549/25000000000000 : ℝ)^49 := by
    have hnat : (6636118299 : ℕ)^65*25000000000000^49 ≤ 14511210312549^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6636118299 10000000000 14511210312549 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(118920389/250000000 : ℝ), (-246777689/2500000000 : ℝ), (-6636118299/10000000000 : ℝ)] ![(18660368454637/50000000000000 : ℝ), (4634421824407/100000000000000 : ℝ), (14511210312549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(118920389/250000000 : ℝ)|^65 ≤ (18660368454637/50000000000000 : ℝ)^49
        have hw : |(118920389/250000000 : ℝ)|=(118920389/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246777689/2500000000 : ℝ)|^65 ≤ (4634421824407/100000000000000 : ℝ)^49
        have hw : |(-246777689/2500000000 : ℝ)|=(246777689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6636118299/10000000000 : ℝ)|^65 ≤ (14511210312549/25000000000000 : ℝ)^49
        have hw : |(-6636118299/10000000000 : ℝ)|=(6636118299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4284125113/10000000000 : ℝ)*x 0 + (3648388049/5000000000 : ℝ)*x 1 + (46036409/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284125113/10000000000 : ℝ)^65 ≤ (16241415267051/50000000000000 : ℝ)^49 := by
    have hnat : (4284125113 : ℕ)^65*50000000000000^49 ≤ 16241415267051^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284125113 10000000000 16241415267051 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3648388049/5000000000 : ℝ)^65 ≤ (32916156054907/50000000000000 : ℝ)^49 := by
    have hnat : (3648388049 : ℕ)^65*50000000000000^49 ≤ 32916156054907^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3648388049 5000000000 32916156054907 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46036409/1000000000 : ℝ)^65 ≤ (1684857340713/100000000000000 : ℝ)^49 := by
    have hnat : (46036409 : ℕ)^65*100000000000000^49 ≤ 1684857340713^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46036409 1000000000 1684857340713 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284125113/10000000000 : ℝ), (3648388049/5000000000 : ℝ), (46036409/1000000000 : ℝ)] ![(16241415267051/50000000000000 : ℝ), (32916156054907/50000000000000 : ℝ), (1684857340713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284125113/10000000000 : ℝ)|^65 ≤ (16241415267051/50000000000000 : ℝ)^49
        have hw : |(4284125113/10000000000 : ℝ)|=(4284125113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3648388049/5000000000 : ℝ)|^65 ≤ (32916156054907/50000000000000 : ℝ)^49
        have hw : |(3648388049/5000000000 : ℝ)|=(3648388049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46036409/1000000000 : ℝ)|^65 ≤ (1684857340713/100000000000000 : ℝ)^49
        have hw : |(46036409/1000000000 : ℝ)|=(46036409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (450378471/1000000000 : ℝ)*x 0 + (7038150089/10000000000 : ℝ)*x 1 + (-626288703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450378471/1000000000 : ℝ)^65 ≤ (17355219684693/50000000000000 : ℝ)^49 := by
    have hnat : (450378471 : ℕ)^65*50000000000000^49 ≤ 17355219684693^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450378471 1000000000 17355219684693 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7038150089/10000000000 : ℝ)^65 ≤ (12551021052831/20000000000000 : ℝ)^49 := by
    have hnat : (7038150089 : ℕ)^65*20000000000000^49 ≤ 12551021052831^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7038150089 10000000000 12551021052831 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626288703/10000000000 : ℝ)^65 ≤ (63361383701/2500000000000 : ℝ)^49 := by
    have hnat : (626288703 : ℕ)^65*2500000000000^49 ≤ 63361383701^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626288703 10000000000 63361383701 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(450378471/1000000000 : ℝ), (7038150089/10000000000 : ℝ), (-626288703/10000000000 : ℝ)] ![(17355219684693/50000000000000 : ℝ), (12551021052831/20000000000000 : ℝ), (63361383701/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(450378471/1000000000 : ℝ)|^65 ≤ (17355219684693/50000000000000 : ℝ)^49
        have hw : |(450378471/1000000000 : ℝ)|=(450378471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7038150089/10000000000 : ℝ)|^65 ≤ (12551021052831/20000000000000 : ℝ)^49
        have hw : |(7038150089/10000000000 : ℝ)|=(7038150089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-626288703/10000000000 : ℝ)|^65 ≤ (63361383701/2500000000000 : ℝ)^49
        have hw : |(-626288703/10000000000 : ℝ)|=(626288703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1405051/10000000000 : ℝ)*x 0 + (3436774277/10000000000 : ℝ)*x 1 + (-2027752473/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1405051/10000000000 : ℝ)^65 ≤ (775881913/100000000000000 : ℝ)^49 := by
    have hnat : (1405051 : ℕ)^65*100000000000000^49 ≤ 775881913^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405051 10000000000 775881913 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3436774277/10000000000 : ℝ)^65 ≤ (24248792330871/100000000000000 : ℝ)^49 := by
    have hnat : (3436774277 : ℕ)^65*100000000000000^49 ≤ 24248792330871^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3436774277 10000000000 24248792330871 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2027752473/2500000000 : ℝ)^65 ≤ (75750431771589/100000000000000 : ℝ)^49 := by
    have hnat : (2027752473 : ℕ)^65*100000000000000^49 ≤ 75750431771589^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027752473 2500000000 75750431771589 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1405051/10000000000 : ℝ), (3436774277/10000000000 : ℝ), (-2027752473/2500000000 : ℝ)] ![(775881913/100000000000000 : ℝ), (24248792330871/100000000000000 : ℝ), (75750431771589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1405051/10000000000 : ℝ)|^65 ≤ (775881913/100000000000000 : ℝ)^49
        have hw : |(-1405051/10000000000 : ℝ)|=(1405051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3436774277/10000000000 : ℝ)|^65 ≤ (24248792330871/100000000000000 : ℝ)^49
        have hw : |(3436774277/10000000000 : ℝ)|=(3436774277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2027752473/2500000000 : ℝ)|^65 ≤ (75750431771589/100000000000000 : ℝ)^49
        have hw : |(-2027752473/2500000000 : ℝ)|=(2027752473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (832253891/2000000000 : ℝ)*x 0 + (-448430091/2500000000 : ℝ)*x 1 + (-333817639/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (832253891/2000000000 : ℝ)^65 ≤ (31252978886983/100000000000000 : ℝ)^49 := by
    have hnat : (832253891 : ℕ)^65*100000000000000^49 ≤ 31252978886983^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832253891 2000000000 31252978886983 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448430091/2500000000 : ℝ)^65 ≤ (102348814501/1000000000000 : ℝ)^49 := by
    have hnat : (448430091 : ℕ)^65*1000000000000^49 ≤ 102348814501^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448430091 2500000000 102348814501 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333817639/500000000 : ℝ)^65 ≤ (2340485585747/4000000000000 : ℝ)^49 := by
    have hnat : (333817639 : ℕ)^65*4000000000000^49 ≤ 2340485585747^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333817639 500000000 2340485585747 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(832253891/2000000000 : ℝ), (-448430091/2500000000 : ℝ), (-333817639/500000000 : ℝ)] ![(31252978886983/100000000000000 : ℝ), (102348814501/1000000000000 : ℝ), (2340485585747/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(832253891/2000000000 : ℝ)|^65 ≤ (31252978886983/100000000000000 : ℝ)^49
        have hw : |(832253891/2000000000 : ℝ)|=(832253891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-448430091/2500000000 : ℝ)|^65 ≤ (102348814501/1000000000000 : ℝ)^49
        have hw : |(-448430091/2500000000 : ℝ)|=(448430091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-333817639/500000000 : ℝ)|^65 ≤ (2340485585747/4000000000000 : ℝ)^49
        have hw : |(-333817639/500000000 : ℝ)|=(333817639/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7439621759/10000000000 : ℝ)*x 0 + (3990496451/10000000000 : ℝ)*x 1 + (691358263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7439621759/10000000000 : ℝ)^65 ≤ (67547344205343/100000000000000 : ℝ)^49 := by
    have hnat : (7439621759 : ℕ)^65*100000000000000^49 ≤ 67547344205343^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7439621759 10000000000 67547344205343 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3990496451/10000000000 : ℝ)^65 ≤ (29563102402759/100000000000000 : ℝ)^49 := by
    have hnat : (3990496451 : ℕ)^65*100000000000000^49 ≤ 29563102402759^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3990496451 10000000000 29563102402759 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691358263/10000000000 : ℝ)^65 ≤ (1444776682601/50000000000000 : ℝ)^49 := by
    have hnat : (691358263 : ℕ)^65*50000000000000^49 ≤ 1444776682601^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691358263 10000000000 1444776682601 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7439621759/10000000000 : ℝ), (3990496451/10000000000 : ℝ), (691358263/10000000000 : ℝ)] ![(67547344205343/100000000000000 : ℝ), (29563102402759/100000000000000 : ℝ), (1444776682601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7439621759/10000000000 : ℝ)|^65 ≤ (67547344205343/100000000000000 : ℝ)^49
        have hw : |(7439621759/10000000000 : ℝ)|=(7439621759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3990496451/10000000000 : ℝ)|^65 ≤ (29563102402759/100000000000000 : ℝ)^49
        have hw : |(3990496451/10000000000 : ℝ)|=(3990496451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(691358263/10000000000 : ℝ)|^65 ≤ (1444776682601/50000000000000 : ℝ)^49
        have hw : |(691358263/10000000000 : ℝ)|=(691358263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (691354921/1000000000 : ℝ)*x 0 + (4350353193/10000000000 : ℝ)*x 1 + (-141615527/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (691354921/1000000000 : ℝ)^65 ≤ (61285614766131/100000000000000 : ℝ)^49 := by
    have hnat : (691354921 : ℕ)^65*100000000000000^49 ≤ 61285614766131^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691354921 1000000000 61285614766131 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4350353193/10000000000 : ℝ)^65 ≤ (33150623948197/100000000000000 : ℝ)^49 := by
    have hnat : (4350353193 : ℕ)^65*100000000000000^49 ≤ 33150623948197^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350353193 10000000000 33150623948197 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141615527/1250000000 : ℝ)^65 ≤ (5563761276971/100000000000000 : ℝ)^49 := by
    have hnat : (141615527 : ℕ)^65*100000000000000^49 ≤ 5563761276971^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141615527 1250000000 5563761276971 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(691354921/1000000000 : ℝ), (4350353193/10000000000 : ℝ), (-141615527/1250000000 : ℝ)] ![(61285614766131/100000000000000 : ℝ), (33150623948197/100000000000000 : ℝ), (5563761276971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(691354921/1000000000 : ℝ)|^65 ≤ (61285614766131/100000000000000 : ℝ)^49
        have hw : |(691354921/1000000000 : ℝ)|=(691354921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4350353193/10000000000 : ℝ)|^65 ≤ (33150623948197/100000000000000 : ℝ)^49
        have hw : |(4350353193/10000000000 : ℝ)|=(4350353193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141615527/1250000000 : ℝ)|^65 ≤ (5563761276971/100000000000000 : ℝ)^49
        have hw : |(-141615527/1250000000 : ℝ)|=(141615527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (10646619/10000000000 : ℝ)*x 0 + (5700836253/10000000000 : ℝ)*x 1 + (-6155705707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10646619/10000000000 : ℝ)^65 ≤ (5694758841/50000000000000 : ℝ)^49 := by
    have hnat : (10646619 : ℕ)^65*50000000000000^49 ≤ 5694758841^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10646619 10000000000 5694758841 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5700836253/10000000000 : ℝ)^65 ≤ (23725481876421/50000000000000 : ℝ)^49 := by
    have hnat : (5700836253 : ℕ)^65*50000000000000^49 ≤ 23725481876421^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5700836253 10000000000 23725481876421 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6155705707/10000000000 : ℝ)^65 ≤ (52537646713369/100000000000000 : ℝ)^49 := by
    have hnat : (6155705707 : ℕ)^65*100000000000000^49 ≤ 52537646713369^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6155705707 10000000000 52537646713369 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10646619/10000000000 : ℝ), (5700836253/10000000000 : ℝ), (-6155705707/10000000000 : ℝ)] ![(5694758841/50000000000000 : ℝ), (23725481876421/50000000000000 : ℝ), (52537646713369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10646619/10000000000 : ℝ)|^65 ≤ (5694758841/50000000000000 : ℝ)^49
        have hw : |(10646619/10000000000 : ℝ)|=(10646619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5700836253/10000000000 : ℝ)|^65 ≤ (23725481876421/50000000000000 : ℝ)^49
        have hw : |(5700836253/10000000000 : ℝ)|=(5700836253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6155705707/10000000000 : ℝ)|^65 ≤ (52537646713369/100000000000000 : ℝ)^49
        have hw : |(-6155705707/10000000000 : ℝ)|=(6155705707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3586339951/5000000000 : ℝ)*x 0 + (-39403267/250000000 : ℝ)*x 1 + (-3729634419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3586339951/5000000000 : ℝ)^65 ≤ (32175627812173/50000000000000 : ℝ)^49 := by
    have hnat : (3586339951 : ℕ)^65*50000000000000^49 ≤ 32175627812173^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3586339951 5000000000 32175627812173 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39403267/250000000 : ℝ)^65 ≤ (2155368486381/25000000000000 : ℝ)^49 := by
    have hnat : (39403267 : ℕ)^65*25000000000000^49 ≤ 2155368486381^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39403267 250000000 2155368486381 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3729634419/10000000000 : ℝ)^65 ≤ (27027270425349/100000000000000 : ℝ)^49 := by
    have hnat : (3729634419 : ℕ)^65*100000000000000^49 ≤ 27027270425349^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3729634419 10000000000 27027270425349 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3586339951/5000000000 : ℝ), (-39403267/250000000 : ℝ), (-3729634419/10000000000 : ℝ)] ![(32175627812173/50000000000000 : ℝ), (2155368486381/25000000000000 : ℝ), (27027270425349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3586339951/5000000000 : ℝ)|^65 ≤ (32175627812173/50000000000000 : ℝ)^49
        have hw : |(3586339951/5000000000 : ℝ)|=(3586339951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-39403267/250000000 : ℝ)|^65 ≤ (2155368486381/25000000000000 : ℝ)^49
        have hw : |(-39403267/250000000 : ℝ)|=(39403267/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3729634419/10000000000 : ℝ)|^65 ≤ (27027270425349/100000000000000 : ℝ)^49
        have hw : |(-3729634419/10000000000 : ℝ)|=(3729634419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (289221829/625000000 : ℝ)*x 0 + (152116739/250000000 : ℝ)*x 1 + (514557743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (289221829/625000000 : ℝ)^65 ≤ (35981389007289/100000000000000 : ℝ)^49 := by
    have hnat : (289221829 : ℕ)^65*100000000000000^49 ≤ 35981389007289^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289221829 625000000 35981389007289 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152116739/250000000 : ℝ)^65 ≤ (5173491892607/10000000000000 : ℝ)^49 := by
    have hnat : (152116739 : ℕ)^65*10000000000000^49 ≤ 5173491892607^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152116739 250000000 5173491892607 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514557743/2500000000 : ℝ)^65 ≤ (6141846025613/50000000000000 : ℝ)^49 := by
    have hnat : (514557743 : ℕ)^65*50000000000000^49 ≤ 6141846025613^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514557743 2500000000 6141846025613 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(289221829/625000000 : ℝ), (152116739/250000000 : ℝ), (514557743/2500000000 : ℝ)] ![(35981389007289/100000000000000 : ℝ), (5173491892607/10000000000000 : ℝ), (6141846025613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(289221829/625000000 : ℝ)|^65 ≤ (35981389007289/100000000000000 : ℝ)^49
        have hw : |(289221829/625000000 : ℝ)|=(289221829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(152116739/250000000 : ℝ)|^65 ≤ (5173491892607/10000000000000 : ℝ)^49
        have hw : |(152116739/250000000 : ℝ)|=(152116739/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514557743/2500000000 : ℝ)|^65 ≤ (6141846025613/50000000000000 : ℝ)^49
        have hw : |(514557743/2500000000 : ℝ)|=(514557743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s3_s3_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1658377601/2500000000 : ℝ)*x 0 + (4285244063/10000000000 : ℝ)*x 1 + (-1694579579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1658377601/2500000000 : ℝ)^65 ≤ (58014584030501/100000000000000 : ℝ)^49 := by
    have hnat : (1658377601 : ℕ)^65*100000000000000^49 ≤ 58014584030501^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1658377601 2500000000 58014584030501 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4285244063/10000000000 : ℝ)^65 ≤ (8123521336209/25000000000000 : ℝ)^49 := by
    have hnat : (4285244063 : ℕ)^65*25000000000000^49 ≤ 8123521336209^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285244063 10000000000 8123521336209 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1694579579/10000000000 : ℝ)^65 ≤ (1186416325493/12500000000000 : ℝ)^49 := by
    have hnat : (1694579579 : ℕ)^65*12500000000000^49 ≤ 1186416325493^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694579579 10000000000 1186416325493 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1658377601/2500000000 : ℝ), (4285244063/10000000000 : ℝ), (-1694579579/10000000000 : ℝ)] ![(58014584030501/100000000000000 : ℝ), (8123521336209/25000000000000 : ℝ), (1186416325493/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1658377601/2500000000 : ℝ)|^65 ≤ (58014584030501/100000000000000 : ℝ)^49
        have hw : |(1658377601/2500000000 : ℝ)|=(1658377601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4285244063/10000000000 : ℝ)|^65 ≤ (8123521336209/25000000000000 : ℝ)^49
        have hw : |(4285244063/10000000000 : ℝ)|=(4285244063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1694579579/10000000000 : ℝ)|^65 ≤ (1186416325493/12500000000000 : ℝ)^49
        have hw : |(-1694579579/10000000000 : ℝ)|=(1694579579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301054_s3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((38977/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38977/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40981/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40981/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-81/125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-81/125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((64959/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64959/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68271/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(68271/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10543/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10543/20000 : ℝ)*X 1 2) := by
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
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  have s3_pow0 : (38977/50000 : ℝ) ^ (129/32 : ℝ) ≤ (1832076371001219877/5000000000000000000 : ℝ) := by
    have hpowers : (38977/50000 : ℝ)^129 ≤ (1832076371001219877/5000000000000000000 : ℝ)^32 := by
      have hnat : (38977 : ℕ)^129*5000000000000000000^32 ≤ 1832076371001219877^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38977 50000 1832076371001219877 5000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38977/50000 : ℝ)) (X := (1832076371001219877/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (6832076371001219877/5000000000000000000 : ℝ) ≤ (10805202734594017/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (6832076371001219877/5000000000000000000 : ℝ)^32 ≤ (10805202734594017/10000000000000000 : ℝ)^129 := by
      have hnat : (6832076371001219877 : ℕ)^32*10000000000000000^129 ≤ 10805202734594017^129*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6832076371001219877 5000000000000000000 10805202734594017 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10805202734594017/10000000000000000 : ℝ)) (X := (6832076371001219877/5000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (4332076371001219877/2500000000000000000 : ℝ) ≤ (11461100434195963/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (4332076371001219877/2500000000000000000 : ℝ)^32 ≤ (11461100434195963/10000000000000000 : ℝ)^129 := by
      have hnat : (4332076371001219877 : ℕ)^32*10000000000000000^129 ≤ 11461100434195963^129*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4332076371001219877 2500000000000000000 11461100434195963 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11461100434195963/10000000000000000 : ℝ)) (X := (4332076371001219877/2500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(805202734594017/7795400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(327948849800973/3897700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (38977/50000 : ℝ)) (alpha := (805202734594017/7795400000000000 : ℝ)) (beta := (327948849800973/3897700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (38977/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(805202734594017/7795400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(327948849800973/3897700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (40981/50000 : ℝ) ^ (129/32 : ℝ) ≤ (44848774603215203009/100000000000000000000 : ℝ) := by
    have hpowers : (40981/50000 : ℝ)^129 ≤ (44848774603215203009/100000000000000000000 : ℝ)^32 := by
      have hnat : (40981 : ℕ)^129*100000000000000000000^32 ≤ 44848774603215203009^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40981 50000 44848774603215203009 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40981/50000 : ℝ)) (X := (44848774603215203009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (144848774603215203009/100000000000000000000 : ℝ) ≤ (5481341497818337/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (144848774603215203009/100000000000000000000 : ℝ)^32 ≤ (5481341497818337/5000000000000000 : ℝ)^129 := by
      have hnat : (144848774603215203009 : ℕ)^32*5000000000000000^129 ≤ 5481341497818337^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        144848774603215203009 100000000000000000000 5481341497818337 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5481341497818337/5000000000000000 : ℝ)) (X := (144848774603215203009/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (94848774603215203009/50000000000000000000 : ℝ) ≤ (2930330189420577/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (94848774603215203009/50000000000000000000 : ℝ)^32 ≤ (2930330189420577/2500000000000000 : ℝ)^129 := by
      have hnat : (94848774603215203009 : ℕ)^32*2500000000000000^129 ≤ 2930330189420577^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94848774603215203009 50000000000000000000 2930330189420577 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2930330189420577/2500000000000000 : ℝ)) (X := (94848774603215203009/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(481341497818337/4098100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(379318881022817/4098100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (40981/50000 : ℝ)) (alpha := (481341497818337/4098100000000000 : ℝ)) (beta := (379318881022817/4098100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (40981/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(481341497818337/4098100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(379318881022817/4098100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (81/125 : ℝ) ^ (129/32 : ℝ) ≤ (543577865692960927/3125000000000000000 : ℝ) := by
    have hpowers : (81/125 : ℝ)^129 ≤ (543577865692960927/3125000000000000000 : ℝ)^32 := by
      have hnat : (81 : ℕ)^129*3125000000000000000^32 ≤ 543577865692960927^32*125^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81 125 543577865692960927 3125000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81/125 : ℝ)) (X := (543577865692960927/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (3668577865692960927/3125000000000000000 : ℝ) ≤ (10405835443401817/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3668577865692960927/3125000000000000000 : ℝ)^32 ≤ (10405835443401817/10000000000000000 : ℝ)^129 := by
      have hnat : (3668577865692960927 : ℕ)^32*10000000000000000^129 ≤ 10405835443401817^129*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3668577865692960927 3125000000000000000 10405835443401817 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10405835443401817/10000000000000000 : ℝ)) (X := (3668577865692960927/3125000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (2106077865692960927/1562500000000000000 : ℝ) ≤ (10768676516180739/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2106077865692960927/1562500000000000000 : ℝ)^32 ≤ (10768676516180739/10000000000000000 : ℝ)^129 := by
      have hnat : (2106077865692960927 : ℕ)^32*10000000000000000^129 ≤ 10768676516180739^129*1562500000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2106077865692960927 1562500000000000000 10768676516180739 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10768676516180739/10000000000000000 : ℝ)) (X := (2106077865692960927/1562500000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(135278481133939/2160000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(181420536389461/3240000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (81/125 : ℝ)) (alpha := (135278481133939/2160000000000000 : ℝ)) (beta := (181420536389461/3240000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (81/125 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(135278481133939/2160000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(181420536389461/3240000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_1 : ((5755529209/10000000000 : ℝ)*X 1 0+(-531476917/2500000000 : ℝ)*X 1 1+(-4928867137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((1380700061/2500000000 : ℝ)*X 2 0+(108948901/200000000 : ℝ)*X 2 1+(43502527/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((5413611911/10000000000 : ℝ)*X 0 0+(334736439/625000000 : ℝ)*X 0 1+(-404833129/2000000000 : ℝ)*X 0 2+(5413611911/10000000000 : ℝ)*X 1 0+(334736439/625000000 : ℝ)*X 1 1+(-404833129/2000000000 : ℝ)*X 1 2+(5413611911/10000000000 : ℝ)*X 2 0+(334736439/625000000 : ℝ)*X 2 1+(-404833129/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-165034959/5000000000 : ℝ)*X 0 0+(1615733537/5000000000 : ℝ)*X 0 1+(-15970877/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((118920389/250000000 : ℝ)*X 1 0+(-246777689/2500000000 : ℝ)*X 1 1+(-6636118299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4284125113/10000000000 : ℝ)*X 2 0+(3648388049/5000000000 : ℝ)*X 2 1+(46036409/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((450378471/1000000000 : ℝ)*X 0 0+(7038150089/10000000000 : ℝ)*X 0 1+(-626288703/10000000000 : ℝ)*X 0 2+(450378471/1000000000 : ℝ)*X 1 0+(7038150089/10000000000 : ℝ)*X 1 1+(-626288703/10000000000 : ℝ)*X 1 2+(450378471/1000000000 : ℝ)*X 2 0+(7038150089/10000000000 : ℝ)*X 2 1+(-626288703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1405051/10000000000 : ℝ)*X 0 0+(3436774277/10000000000 : ℝ)*X 0 1+(-2027752473/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((832253891/2000000000 : ℝ)*X 1 0+(-448430091/2500000000 : ℝ)*X 1 1+(-333817639/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((7439621759/10000000000 : ℝ)*X 2 0+(3990496451/10000000000 : ℝ)*X 2 1+(691358263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((691354921/1000000000 : ℝ)*X 0 0+(4350353193/10000000000 : ℝ)*X 0 1+(-141615527/1250000000 : ℝ)*X 0 2+(691354921/1000000000 : ℝ)*X 1 0+(4350353193/10000000000 : ℝ)*X 1 1+(-141615527/1250000000 : ℝ)*X 1 2+(691354921/1000000000 : ℝ)*X 2 0+(4350353193/10000000000 : ℝ)*X 2 1+(-141615527/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((10646619/10000000000 : ℝ)*X 0 0+(5700836253/10000000000 : ℝ)*X 0 1+(-6155705707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((3586339951/5000000000 : ℝ)*X 1 0+(-39403267/250000000 : ℝ)*X 1 1+(-3729634419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((289221829/625000000 : ℝ)*X 2 0+(152116739/250000000 : ℝ)*X 2 1+(514557743/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((1658377601/2500000000 : ℝ)*X 0 0+(4285244063/10000000000 : ℝ)*X 0 1+(-1694579579/10000000000 : ℝ)*X 0 2+(1658377601/2500000000 : ℝ)*X 1 0+(4285244063/10000000000 : ℝ)*X 1 1+(-1694579579/10000000000 : ℝ)*X 1 2+(1658377601/2500000000 : ℝ)*X 2 0+(4285244063/10000000000 : ℝ)*X 2 1+(-1694579579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((64959/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64959/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1349448541059546672488128549967/86255087598000000000000000000000000 : ℝ) := by norm_num
    linear_combination (205657278329/1000000000000 : ℝ)*(base7) + (14238936383/250000000000 : ℝ)*(base39) + (3226440989/10000000000 : ℝ)*(base60) + (699754656671/250000000000 : ℝ)*(major_s3_0) + (699754656671/250000000000 : ℝ)*(major_s3_1) + (699754656671/250000000000 : ℝ)*(major_s3_2) + (16811/25000000000 : ℝ)*(sp_s3_6) + (715776815521/200000000000 : ℝ)*(sp_s3_7) + (715829902649/200000000000 : ℝ)*(sp_s3_8) + (894787898789/250000000000 : ℝ)*(sp_s3_9) + (419571415643/200000000000 : ℝ)*(sp_s3_13) + (54988893/200000000000 : ℝ)*(sp_s3_14) + (380353/40000000000 : ℝ)*(sp_s3_22) + (3713457/500000000000 : ℝ)*(sp_s3_23) + (946100236163/500000000000 : ℝ)*(f.failure) + (357915902207/100000000000 : ℝ)*(f.sum) + (8428631248438897889/22129740000000000000000000000000 : ℝ)*base63 + (323522618125669/810000000000000000000000000 : ℝ)*base64 + (489535074802689/2049050000000000000000000000 : ℝ)*base66 + (294465057497069/540000000000000000000000000 : ℝ)*base69 + (19219991388348292213/31571370000000000000000000000000 : ℝ)*base70 + (913996448283859/1948850000000000000000000000 : ℝ)*base72 + (29024854322073/256131250000000000000000000 : ℝ)*base75 + (54689963991763/487212500000000000000000000 : ℝ)*base77 + (22328414157800986087/79865821850000000000000000000000 : ℝ)*base78 + (6097/12500000000000000 : ℝ)*base86 + (6097/12500000000000000 : ℝ)*base88 + (6097/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68271/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(68271/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1720076527706465216755229593027/86255087598000000000000000000000000 : ℝ) := by norm_num
    linear_combination (405299633099/1000000000000 : ℝ)*(base7) + (150439/250000000000 : ℝ)*(base39) + (11302033703/200000000000 : ℝ)*(base60) + (675953158949/250000000000 : ℝ)*(major_s3_0) + (675953158949/250000000000 : ℝ)*(major_s3_1) + (675953158949/250000000000 : ℝ)*(major_s3_2) + (3956567/500000000000 : ℝ)*(sp_s3_1) + (1473439/12500000000 : ℝ)*(sp_s3_8) + (3330130556963/1000000000000 : ℝ)*(sp_s3_14) + (3330013530429/1000000000000 : ℝ)*(sp_s3_15) + (832534829671/250000000000 : ℝ)*(sp_s3_16) + (2233113153659/1000000000000 : ℝ)*(sp_s3_20) + (8761721/1000000000000 : ℝ)*(sp_s3_21) + (6382271/250000000000 : ℝ)*(sp_s3_27) + (365567809929/200000000000 : ℝ)*(f.failure) + (832534829671/250000000000 : ℝ)*(f.sum) + (3949607644139308309/22129740000000000000000000000000 : ℝ)*base62 + (5979786353489/810000000000000000000000000 : ℝ)*base65 + (1127984281572649/2049050000000000000000000000 : ℝ)*base67 + (58701035787889/540000000000000000000000000 : ℝ)*base68 + (10013161640741319353/31571370000000000000000000000000 : ℝ)*base71 + (31465188124899/121803125000000000000000000 : ℝ)*base73 + (101107363142323/256131250000000000000000000 : ℝ)*base74 + (318705330325561/974425000000000000000000000 : ℝ)*base76 + (3335663369958732659/9983227731250000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (4349/5000000000000000 : ℝ)*base87 + (4349/5000000000000000 : ℝ)*base89 + (4349/5000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10543/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10543/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (163694120343890396090552823/31946328740000000000000000000000 : ℝ) := by norm_num
    linear_combination (50520027829/125000000000 : ℝ)*(base7) + (331808954469/1000000000000 : ℝ)*(base39) + (2714070270129/1000000000000 : ℝ)*(major_s3_0) + (2714070270129/1000000000000 : ℝ)*(major_s3_1) + (2714070270129/1000000000000 : ℝ)*(major_s3_2) + (15769/500000000000 : ℝ)*(sp_s3_1) + (22314237/1000000000000 : ℝ)*(sp_s3_2) + (8094069/1000000000000 : ℝ)*(sp_s3_6) + (2864443/250000000000 : ℝ)*(sp_s3_9) + (1717003/40000000000 : ℝ)*(sp_s3_20) + (836106735039/250000000000 : ℝ)*(sp_s3_21) + (1672213454309/500000000000 : ℝ)*(sp_s3_22) + (836098292037/250000000000 : ℝ)*(sp_s3_23) + (2238882648047/1000000000000 : ℝ)*(sp_s3_27) + (1834773444559/1000000000000 : ℝ)*(f.failure) + (836106735039/250000000000 : ℝ)*(f.sum) + (1187246632540007563/29506320000000000000000000000000 : ℝ)*base62 + (374600293756823/1080000000000000000000000000 : ℝ)*base65 + (1578345529293293/4098100000000000000000000000 : ℝ)*base66 + (217805067069377/720000000000000000000000000 : ℝ)*base69 + (1276483530342595729/42095160000000000000000000000000 : ℝ)*base70 + (476761388664663/3897700000000000000000000000 : ℝ)*base72 + (907860168655257/4098100000000000000000000000 : ℝ)*base74 + (2050305111061927/7795400000000000000000000000 : ℝ)*base76 + (2739694548541245339/39932910925000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (11379/25000000000000000 : ℝ)*base87 + (11379/25000000000000000 : ℝ)*base89 + (11379/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((38977/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38977/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40981/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40981/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-81/125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-81/125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((64959/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64959/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68271/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(68271/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10543/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10543/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301054_s3 p hpa hpb X hX hprev2

#print axioms solution
