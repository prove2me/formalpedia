-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311055_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:59:19.508212+00:00
-- url     : https://prove2.me/submissions/6272911e-d584-4e6b-8fef-050cbdb4ee9b

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
theorem collision_support_c311055_s3_s3_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164599019/10000000000 : ℝ)*x 0 + (5606872621/10000000000 : ℝ)*x 1 + (4759250627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164599019/10000000000 : ℝ)^9 ≤ (1397929604569/10000000000000 : ℝ)^7 := by
    have hnat : (2164599019 : ℕ)^9*10000000000000^7 ≤ 1397929604569^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164599019 10000000000 1397929604569 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5606872621/10000000000 : ℝ)^9 ≤ (47525489765477/100000000000000 : ℝ)^7 := by
    have hnat : (5606872621 : ℕ)^9*100000000000000^7 ≤ 47525489765477^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5606872621 10000000000 47525489765477 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4759250627/10000000000 : ℝ)^9 ≤ (19247607090047/50000000000000 : ℝ)^7 := by
    have hnat : (4759250627 : ℕ)^9*50000000000000^7 ≤ 19247607090047^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4759250627 10000000000 19247607090047 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164599019/10000000000 : ℝ), (5606872621/10000000000 : ℝ), (4759250627/10000000000 : ℝ)] ![(1397929604569/10000000000000 : ℝ), (47525489765477/100000000000000 : ℝ), (19247607090047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164599019/10000000000 : ℝ)|^9 ≤ (1397929604569/10000000000000 : ℝ)^7
        have hw : |(-2164599019/10000000000 : ℝ)|=(2164599019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5606872621/10000000000 : ℝ)|^9 ≤ (47525489765477/100000000000000 : ℝ)^7
        have hw : |(5606872621/10000000000 : ℝ)|=(5606872621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4759250627/10000000000 : ℝ)|^9 ≤ (19247607090047/50000000000000 : ℝ)^7
        have hw : |(4759250627/10000000000 : ℝ)|=(4759250627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4763904437/10000000000 : ℝ)*x 0 + (-660155991/5000000000 : ℝ)*x 1 + (6197149763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4763904437/10000000000 : ℝ)^9 ≤ (602244035247/1562500000000 : ℝ)^7 := by
    have hnat : (4763904437 : ℕ)^9*1562500000000^7 ≤ 602244035247^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4763904437 10000000000 602244035247 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660155991/5000000000 : ℝ)^9 ≤ (7403571881409/100000000000000 : ℝ)^7 := by
    have hnat : (660155991 : ℕ)^9*100000000000000^7 ≤ 7403571881409^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660155991 5000000000 7403571881409 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6197149763/10000000000 : ℝ)^9 ≤ (54052809844617/100000000000000 : ℝ)^7 := by
    have hnat : (6197149763 : ℕ)^9*100000000000000^7 ≤ 54052809844617^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6197149763 10000000000 54052809844617 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4763904437/10000000000 : ℝ), (-660155991/5000000000 : ℝ), (6197149763/10000000000 : ℝ)] ![(602244035247/1562500000000 : ℝ), (7403571881409/100000000000000 : ℝ), (54052809844617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4763904437/10000000000 : ℝ)|^9 ≤ (602244035247/1562500000000 : ℝ)^7
        have hw : |(4763904437/10000000000 : ℝ)|=(4763904437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-660155991/5000000000 : ℝ)|^9 ≤ (7403571881409/100000000000000 : ℝ)^7
        have hw : |(-660155991/5000000000 : ℝ)|=(660155991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6197149763/10000000000 : ℝ)|^9 ≤ (54052809844617/100000000000000 : ℝ)^7
        have hw : |(6197149763/10000000000 : ℝ)|=(6197149763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4749232883/10000000000 : ℝ)*x 0 + (5605759727/10000000000 : ℝ)*x 1 + (-1089294847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4749232883/10000000000 : ℝ)^9 ≤ (19195532975983/50000000000000 : ℝ)^7 := by
    have hnat : (4749232883 : ℕ)^9*50000000000000^7 ≤ 19195532975983^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4749232883 10000000000 19195532975983 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5605759727/10000000000 : ℝ)^9 ≤ (742396276417/1562500000000 : ℝ)^7 := by
    have hnat : (5605759727 : ℕ)^9*1562500000000^7 ≤ 742396276417^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5605759727 10000000000 742396276417 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089294847/5000000000 : ℝ)^9 ≤ (880973271301/6250000000000 : ℝ)^7 := by
    have hnat : (1089294847 : ℕ)^9*6250000000000^7 ≤ 880973271301^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089294847 5000000000 880973271301 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4749232883/10000000000 : ℝ), (5605759727/10000000000 : ℝ), (-1089294847/5000000000 : ℝ)] ![(19195532975983/50000000000000 : ℝ), (742396276417/1562500000000 : ℝ), (880973271301/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4749232883/10000000000 : ℝ)|^9 ≤ (19195532975983/50000000000000 : ℝ)^7
        have hw : |(4749232883/10000000000 : ℝ)|=(4749232883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5605759727/10000000000 : ℝ)|^9 ≤ (742396276417/1562500000000 : ℝ)^7
        have hw : |(5605759727/10000000000 : ℝ)|=(5605759727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1089294847/5000000000 : ℝ)|^9 ≤ (880973271301/6250000000000 : ℝ)^7
        have hw : |(-1089294847/5000000000 : ℝ)|=(1089294847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5966337783/10000000000 : ℝ)*x 0 + (999025543/2500000000 : ℝ)*x 1 + (2609103839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5966337783/10000000000 : ℝ)^9 ≤ (51478319634189/100000000000000 : ℝ)^7 := by
    have hnat : (5966337783 : ℕ)^9*100000000000000^7 ≤ 51478319634189^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5966337783 10000000000 51478319634189 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999025543/2500000000 : ℝ)^9 ≤ (30748112739129/100000000000000 : ℝ)^7 := by
    have hnat : (999025543 : ℕ)^9*100000000000000^7 ≤ 30748112739129^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999025543 2500000000 30748112739129 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609103839/10000000000 : ℝ)^9 ≤ (17773567611523/100000000000000 : ℝ)^7 := by
    have hnat : (2609103839 : ℕ)^9*100000000000000^7 ≤ 17773567611523^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609103839 10000000000 17773567611523 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5966337783/10000000000 : ℝ), (999025543/2500000000 : ℝ), (2609103839/10000000000 : ℝ)] ![(51478319634189/100000000000000 : ℝ), (30748112739129/100000000000000 : ℝ), (17773567611523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5966337783/10000000000 : ℝ)|^9 ≤ (51478319634189/100000000000000 : ℝ)^7
        have hw : |(5966337783/10000000000 : ℝ)|=(5966337783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999025543/2500000000 : ℝ)|^9 ≤ (30748112739129/100000000000000 : ℝ)^7
        have hw : |(999025543/2500000000 : ℝ)|=(999025543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609103839/10000000000 : ℝ)|^9 ≤ (17773567611523/100000000000000 : ℝ)^7
        have hw : |(2609103839/10000000000 : ℝ)|=(2609103839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-468424633/2500000000 : ℝ)*x 0 + (4937990367/10000000000 : ℝ)*x 1 + (1413147331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (468424633/2500000000 : ℝ)^9 ≤ (5805901183669/50000000000000 : ℝ)^7 := by
    have hnat : (468424633 : ℕ)^9*50000000000000^7 ≤ 5805901183669^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468424633 2500000000 5805901183669 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4937990367/10000000000 : ℝ)^9 ≤ (1009097597759/2500000000000 : ℝ)^7 := by
    have hnat : (4937990367 : ℕ)^9*2500000000000^7 ≤ 1009097597759^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4937990367 10000000000 1009097597759 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1413147331/2500000000 : ℝ)^9 ≤ (1920971748577/4000000000000 : ℝ)^7 := by
    have hnat : (1413147331 : ℕ)^9*4000000000000^7 ≤ 1920971748577^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413147331 2500000000 1920971748577 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-468424633/2500000000 : ℝ), (4937990367/10000000000 : ℝ), (1413147331/2500000000 : ℝ)] ![(5805901183669/50000000000000 : ℝ), (1009097597759/2500000000000 : ℝ), (1920971748577/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-468424633/2500000000 : ℝ)|^9 ≤ (5805901183669/50000000000000 : ℝ)^7
        have hw : |(-468424633/2500000000 : ℝ)|=(468424633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4937990367/10000000000 : ℝ)|^9 ≤ (1009097597759/2500000000000 : ℝ)^7
        have hw : |(4937990367/10000000000 : ℝ)|=(4937990367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1413147331/2500000000 : ℝ)|^9 ≤ (1920971748577/4000000000000 : ℝ)^7
        have hw : |(1413147331/2500000000 : ℝ)|=(1413147331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2302936657/5000000000 : ℝ)*x 0 + (-631328907/10000000000 : ℝ)*x 1 + (6740872309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2302936657/5000000000 : ℝ)^9 ≤ (36907566729539/100000000000000 : ℝ)^7 := by
    have hnat : (2302936657 : ℕ)^9*100000000000000^7 ≤ 36907566729539^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2302936657 5000000000 36907566729539 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (631328907/10000000000 : ℝ)^9 ≤ (573457950037/20000000000000 : ℝ)^7 := by
    have hnat : (631328907 : ℕ)^9*20000000000000^7 ≤ 573457950037^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631328907 10000000000 573457950037 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6740872309/10000000000 : ℝ)^9 ≤ (12045028699337/20000000000000 : ℝ)^7 := by
    have hnat : (6740872309 : ℕ)^9*20000000000000^7 ≤ 12045028699337^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6740872309 10000000000 12045028699337 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2302936657/5000000000 : ℝ), (-631328907/10000000000 : ℝ), (6740872309/10000000000 : ℝ)] ![(36907566729539/100000000000000 : ℝ), (573457950037/20000000000000 : ℝ), (12045028699337/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2302936657/5000000000 : ℝ)|^9 ≤ (36907566729539/100000000000000 : ℝ)^7
        have hw : |(2302936657/5000000000 : ℝ)|=(2302936657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-631328907/10000000000 : ℝ)|^9 ≤ (573457950037/20000000000000 : ℝ)^7
        have hw : |(-631328907/10000000000 : ℝ)|=(631328907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6740872309/10000000000 : ℝ)|^9 ≤ (12045028699337/20000000000000 : ℝ)^7
        have hw : |(6740872309/10000000000 : ℝ)|=(6740872309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4591099117/10000000000 : ℝ)*x 0 + (793220673/1250000000 : ℝ)*x 1 + (-668180211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4591099117/10000000000 : ℝ)^9 ≤ (9188855880241/25000000000000 : ℝ)^7 := by
    have hnat : (4591099117 : ℕ)^9*25000000000000^7 ≤ 9188855880241^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4591099117 10000000000 9188855880241 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (793220673/1250000000 : ℝ)^9 ≤ (55725101946219/100000000000000 : ℝ)^7 := by
    have hnat : (793220673 : ℕ)^9*100000000000000^7 ≤ 55725101946219^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793220673 1250000000 55725101946219 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (668180211/5000000000 : ℝ)^9 ≤ (7519474521119/100000000000000 : ℝ)^7 := by
    have hnat : (668180211 : ℕ)^9*100000000000000^7 ≤ 7519474521119^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668180211 5000000000 7519474521119 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4591099117/10000000000 : ℝ), (793220673/1250000000 : ℝ), (-668180211/5000000000 : ℝ)] ![(9188855880241/25000000000000 : ℝ), (55725101946219/100000000000000 : ℝ), (7519474521119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4591099117/10000000000 : ℝ)|^9 ≤ (9188855880241/25000000000000 : ℝ)^7
        have hw : |(4591099117/10000000000 : ℝ)|=(4591099117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(793220673/1250000000 : ℝ)|^9 ≤ (55725101946219/100000000000000 : ℝ)^7
        have hw : |(793220673/1250000000 : ℝ)|=(793220673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-668180211/5000000000 : ℝ)|^9 ≤ (7519474521119/100000000000000 : ℝ)^7
        have hw : |(-668180211/5000000000 : ℝ)|=(668180211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5264590391/10000000000 : ℝ)*x 0 + (5620271271/10000000000 : ℝ)*x 1 + (1470049817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264590391/10000000000 : ℝ)^9 ≤ (4382828415587/10000000000000 : ℝ)^7 := by
    have hnat : (5264590391 : ℕ)^9*10000000000000^7 ≤ 4382828415587^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264590391 10000000000 4382828415587 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5620271271/10000000000 : ℝ)^9 ≤ (11917889819067/25000000000000 : ℝ)^7 := by
    have hnat : (5620271271 : ℕ)^9*25000000000000^7 ≤ 11917889819067^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620271271 10000000000 11917889819067 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1470049817/10000000000 : ℝ)^9 ≤ (4250078276301/50000000000000 : ℝ)^7 := by
    have hnat : (1470049817 : ℕ)^9*50000000000000^7 ≤ 4250078276301^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470049817 10000000000 4250078276301 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264590391/10000000000 : ℝ), (5620271271/10000000000 : ℝ), (1470049817/10000000000 : ℝ)] ![(4382828415587/10000000000000 : ℝ), (11917889819067/25000000000000 : ℝ), (4250078276301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264590391/10000000000 : ℝ)|^9 ≤ (4382828415587/10000000000000 : ℝ)^7
        have hw : |(5264590391/10000000000 : ℝ)|=(5264590391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5620271271/10000000000 : ℝ)|^9 ≤ (11917889819067/25000000000000 : ℝ)^7
        have hw : |(5620271271/10000000000 : ℝ)|=(5620271271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1470049817/10000000000 : ℝ)|^9 ≤ (4250078276301/50000000000000 : ℝ)^7
        have hw : |(1470049817/10000000000 : ℝ)|=(1470049817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-76508481/625000000 : ℝ)*x 0 + (5299068393/10000000000 : ℝ)*x 1 + (5749439037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76508481/625000000 : ℝ)^9 ≤ (6717527254519/100000000000000 : ℝ)^7 := by
    have hnat : (76508481 : ℕ)^9*100000000000000^7 ≤ 6717527254519^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76508481 625000000 6717527254519 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5299068393/10000000000 : ℝ)^9 ≤ (8839534287229/20000000000000 : ℝ)^7 := by
    have hnat : (5299068393 : ℕ)^9*20000000000000^7 ≤ 8839534287229^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5299068393 10000000000 8839534287229 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5749439037/10000000000 : ℝ)^9 ≤ (24542400646433/50000000000000 : ℝ)^7 := by
    have hnat : (5749439037 : ℕ)^9*50000000000000^7 ≤ 24542400646433^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5749439037 10000000000 24542400646433 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-76508481/625000000 : ℝ), (5299068393/10000000000 : ℝ), (5749439037/10000000000 : ℝ)] ![(6717527254519/100000000000000 : ℝ), (8839534287229/20000000000000 : ℝ), (24542400646433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-76508481/625000000 : ℝ)|^9 ≤ (6717527254519/100000000000000 : ℝ)^7
        have hw : |(-76508481/625000000 : ℝ)|=(76508481/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5299068393/10000000000 : ℝ)|^9 ≤ (8839534287229/20000000000000 : ℝ)^7
        have hw : |(5299068393/10000000000 : ℝ)|=(5299068393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5749439037/10000000000 : ℝ)|^9 ≤ (24542400646433/50000000000000 : ℝ)^7
        have hw : |(5749439037/10000000000 : ℝ)|=(5749439037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4288805997/10000000000 : ℝ)*x 0 + (-572680801/5000000000 : ℝ)*x 1 + (1347030717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288805997/10000000000 : ℝ)^9 ≤ (1052300267349/3125000000000 : ℝ)^7 := by
    have hnat : (4288805997 : ℕ)^9*3125000000000^7 ≤ 1052300267349^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288805997 10000000000 1052300267349 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572680801/5000000000 : ℝ)^9 ≤ (3083465449007/50000000000000 : ℝ)^7 := by
    have hnat : (572680801 : ℕ)^9*50000000000000^7 ≤ 3083465449007^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572680801 5000000000 3083465449007 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347030717/2000000000 : ℝ)^9 ≤ (12031892107787/20000000000000 : ℝ)^7 := by
    have hnat : (1347030717 : ℕ)^9*20000000000000^7 ≤ 12031892107787^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347030717 2000000000 12031892107787 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288805997/10000000000 : ℝ), (-572680801/5000000000 : ℝ), (1347030717/2000000000 : ℝ)] ![(1052300267349/3125000000000 : ℝ), (3083465449007/50000000000000 : ℝ), (12031892107787/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288805997/10000000000 : ℝ)|^9 ≤ (1052300267349/3125000000000 : ℝ)^7
        have hw : |(4288805997/10000000000 : ℝ)|=(4288805997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-572680801/5000000000 : ℝ)|^9 ≤ (3083465449007/50000000000000 : ℝ)^7
        have hw : |(-572680801/5000000000 : ℝ)|=(572680801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347030717/2000000000 : ℝ)|^9 ≤ (12031892107787/20000000000000 : ℝ)^7
        have hw : |(1347030717/2000000000 : ℝ)|=(1347030717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (717578761/1250000000 : ℝ)*x 0 + (2648973987/5000000000 : ℝ)*x 1 + (-619756329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (717578761/1250000000 : ℝ)^9 ≤ (9797626111307/20000000000000 : ℝ)^7 := by
    have hnat : (717578761 : ℕ)^9*20000000000000^7 ≤ 9797626111307^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717578761 1250000000 9797626111307 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2648973987/5000000000 : ℝ)^9 ≤ (22092828385383/50000000000000 : ℝ)^7 := by
    have hnat : (2648973987 : ℕ)^9*50000000000000^7 ≤ 22092828385383^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648973987 5000000000 22092828385383 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (619756329/5000000000 : ℝ)^9 ≤ (273048506233/4000000000000 : ℝ)^7 := by
    have hnat : (619756329 : ℕ)^9*4000000000000^7 ≤ 273048506233^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      619756329 5000000000 273048506233 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(717578761/1250000000 : ℝ), (2648973987/5000000000 : ℝ), (-619756329/5000000000 : ℝ)] ![(9797626111307/20000000000000 : ℝ), (22092828385383/50000000000000 : ℝ), (273048506233/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(717578761/1250000000 : ℝ)|^9 ≤ (9797626111307/20000000000000 : ℝ)^7
        have hw : |(717578761/1250000000 : ℝ)|=(717578761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2648973987/5000000000 : ℝ)|^9 ≤ (22092828385383/50000000000000 : ℝ)^7
        have hw : |(2648973987/5000000000 : ℝ)|=(2648973987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-619756329/5000000000 : ℝ)|^9 ≤ (273048506233/4000000000000 : ℝ)^7
        have hw : |(-619756329/5000000000 : ℝ)|=(619756329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7133131087/10000000000 : ℝ)*x 0 + (3573752917/10000000000 : ℝ)*x 1 + (1483121113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7133131087/10000000000 : ℝ)^9 ≤ (12953593359261/20000000000000 : ℝ)^7 := by
    have hnat : (7133131087 : ℕ)^9*20000000000000^7 ≤ 12953593359261^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7133131087 10000000000 12953593359261 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3573752917/10000000000 : ℝ)^9 ≤ (3329322210961/12500000000000 : ℝ)^7 := by
    have hnat : (3573752917 : ℕ)^9*12500000000000^7 ≤ 3329322210961^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3573752917 10000000000 3329322210961 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1483121113/10000000000 : ℝ)^9 ≤ (53734096873/625000000000 : ℝ)^7 := by
    have hnat : (1483121113 : ℕ)^9*625000000000^7 ≤ 53734096873^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483121113 10000000000 53734096873 625000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7133131087/10000000000 : ℝ), (3573752917/10000000000 : ℝ), (1483121113/10000000000 : ℝ)] ![(12953593359261/20000000000000 : ℝ), (3329322210961/12500000000000 : ℝ), (53734096873/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7133131087/10000000000 : ℝ)|^9 ≤ (12953593359261/20000000000000 : ℝ)^7
        have hw : |(7133131087/10000000000 : ℝ)|=(7133131087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3573752917/10000000000 : ℝ)|^9 ≤ (3329322210961/12500000000000 : ℝ)^7
        have hw : |(3573752917/10000000000 : ℝ)|=(3573752917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1483121113/10000000000 : ℝ)|^9 ≤ (53734096873/625000000000 : ℝ)^7
        have hw : |(1483121113/10000000000 : ℝ)|=(1483121113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1207092409/10000000000 : ℝ)*x 0 + (3104766097/5000000000 : ℝ)*x 1 + (2413958221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1207092409/10000000000 : ℝ)^9 ≤ (1649379816163/25000000000000 : ℝ)^7 := by
    have hnat : (1207092409 : ℕ)^9*25000000000000^7 ≤ 1649379816163^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207092409 10000000000 1649379816163 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104766097/5000000000 : ℝ)^9 ≤ (1083834186097/2000000000000 : ℝ)^7 := by
    have hnat : (3104766097 : ℕ)^9*2000000000000^7 ≤ 1083834186097^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104766097 5000000000 1083834186097 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2413958221/5000000000 : ℝ)^9 ≤ (39210771413789/100000000000000 : ℝ)^7 := by
    have hnat : (2413958221 : ℕ)^9*100000000000000^7 ≤ 39210771413789^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2413958221 5000000000 39210771413789 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1207092409/10000000000 : ℝ), (3104766097/5000000000 : ℝ), (2413958221/5000000000 : ℝ)] ![(1649379816163/25000000000000 : ℝ), (1083834186097/2000000000000 : ℝ), (39210771413789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1207092409/10000000000 : ℝ)|^9 ≤ (1649379816163/25000000000000 : ℝ)^7
        have hw : |(-1207092409/10000000000 : ℝ)|=(1207092409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104766097/5000000000 : ℝ)|^9 ≤ (1083834186097/2000000000000 : ℝ)^7
        have hw : |(3104766097/5000000000 : ℝ)|=(3104766097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2413958221/5000000000 : ℝ)|^9 ≤ (39210771413789/100000000000000 : ℝ)^7
        have hw : |(2413958221/5000000000 : ℝ)|=(2413958221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2886226271/5000000000 : ℝ)*x 0 + (-59764773/1000000000 : ℝ)*x 1 + (5649478129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2886226271/5000000000 : ℝ)^9 ≤ (49337554591347/100000000000000 : ℝ)^7 := by
    have hnat : (2886226271 : ℕ)^9*100000000000000^7 ≤ 49337554591347^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2886226271 5000000000 49337554591347 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (59764773/1000000000 : ℝ)^9 ≤ (334016732167/12500000000000 : ℝ)^7 := by
    have hnat : (59764773 : ℕ)^9*12500000000000^7 ≤ 334016732167^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59764773 1000000000 334016732167 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5649478129/10000000000 : ℝ)^9 ≤ (47990311545043/100000000000000 : ℝ)^7 := by
    have hnat : (5649478129 : ℕ)^9*100000000000000^7 ≤ 47990311545043^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5649478129 10000000000 47990311545043 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2886226271/5000000000 : ℝ), (-59764773/1000000000 : ℝ), (5649478129/10000000000 : ℝ)] ![(49337554591347/100000000000000 : ℝ), (334016732167/12500000000000 : ℝ), (47990311545043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2886226271/5000000000 : ℝ)|^9 ≤ (49337554591347/100000000000000 : ℝ)^7
        have hw : |(2886226271/5000000000 : ℝ)|=(2886226271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-59764773/1000000000 : ℝ)|^9 ≤ (334016732167/12500000000000 : ℝ)^7
        have hw : |(-59764773/1000000000 : ℝ)|=(59764773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5649478129/10000000000 : ℝ)|^9 ≤ (47990311545043/100000000000000 : ℝ)^7
        have hw : |(5649478129/10000000000 : ℝ)|=(5649478129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4224265149/10000000000 : ℝ)*x 0 + (6379448759/10000000000 : ℝ)*x 1 + (-1780025833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224265149/10000000000 : ℝ)^9 ≤ (33023487301733/100000000000000 : ℝ)^7 := by
    have hnat : (4224265149 : ℕ)^9*100000000000000^7 ≤ 33023487301733^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224265149 10000000000 33023487301733 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6379448759/10000000000 : ℝ)^9 ≤ (56105690489057/100000000000000 : ℝ)^7 := by
    have hnat : (6379448759 : ℕ)^9*100000000000000^7 ≤ 56105690489057^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6379448759 10000000000 56105690489057 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1780025833/10000000000 : ℝ)^9 ≤ (2174164438609/20000000000000 : ℝ)^7 := by
    have hnat : (1780025833 : ℕ)^9*20000000000000^7 ≤ 2174164438609^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780025833 10000000000 2174164438609 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224265149/10000000000 : ℝ), (6379448759/10000000000 : ℝ), (-1780025833/10000000000 : ℝ)] ![(33023487301733/100000000000000 : ℝ), (56105690489057/100000000000000 : ℝ), (2174164438609/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224265149/10000000000 : ℝ)|^9 ≤ (33023487301733/100000000000000 : ℝ)^7
        have hw : |(4224265149/10000000000 : ℝ)|=(4224265149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6379448759/10000000000 : ℝ)|^9 ≤ (56105690489057/100000000000000 : ℝ)^7
        have hw : |(6379448759/10000000000 : ℝ)|=(6379448759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1780025833/10000000000 : ℝ)|^9 ≤ (2174164438609/20000000000000 : ℝ)^7
        have hw : |(-1780025833/10000000000 : ℝ)|=(1780025833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s3_s3_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7246932127/10000000000 : ℝ)*x 0 + (339038609/1250000000 : ℝ)*x 1 + (2312355683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7246932127/10000000000 : ℝ)^9 ≤ (6609951139721/10000000000000 : ℝ)^7 := by
    have hnat : (7246932127 : ℕ)^9*10000000000000^7 ≤ 6609951139721^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7246932127 10000000000 6609951139721 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339038609/1250000000 : ℝ)^9 ≤ (18682545257747/100000000000000 : ℝ)^7 := by
    have hnat : (339038609 : ℕ)^9*100000000000000^7 ≤ 18682545257747^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339038609 1250000000 18682545257747 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2312355683/10000000000 : ℝ)^9 ≤ (15217943325319/100000000000000 : ℝ)^7 := by
    have hnat : (2312355683 : ℕ)^9*100000000000000^7 ≤ 15217943325319^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312355683 10000000000 15217943325319 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7246932127/10000000000 : ℝ), (339038609/1250000000 : ℝ), (2312355683/10000000000 : ℝ)] ![(6609951139721/10000000000000 : ℝ), (18682545257747/100000000000000 : ℝ), (15217943325319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7246932127/10000000000 : ℝ)|^9 ≤ (6609951139721/10000000000000 : ℝ)^7
        have hw : |(7246932127/10000000000 : ℝ)|=(7246932127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339038609/1250000000 : ℝ)|^9 ≤ (18682545257747/100000000000000 : ℝ)^7
        have hw : |(339038609/1250000000 : ℝ)|=(339038609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2312355683/10000000000 : ℝ)|^9 ≤ (15217943325319/100000000000000 : ℝ)^7
        have hw : |(2312355683/10000000000 : ℝ)|=(2312355683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311055_s3 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((11099/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11099/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13847/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13847/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28277/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28277/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35487/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35487/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36397/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18001/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18001/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (11099/20000 : ℝ) ^ (71/16 : ℝ) ≤ (7330379935271723523/100000000000000000000 : ℝ) := by
    have hpowers : (11099/20000 : ℝ)^71 ≤ (7330379935271723523/100000000000000000000 : ℝ)^16 := by
      have hnat : (11099 : ℕ)^71*100000000000000000000^16 ≤ 7330379935271723523^16*20000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11099 20000 7330379935271723523 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11099/20000 : ℝ)) (X := (7330379935271723523/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (107330379935271723523/100000000000000000000 : ℝ) ≤ (10160695065075797/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (107330379935271723523/100000000000000000000 : ℝ)^16 ≤ (10160695065075797/10000000000000000 : ℝ)^71 := by
      have hnat : (107330379935271723523 : ℕ)^16*10000000000000000^71 ≤ 10160695065075797^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107330379935271723523 100000000000000000000 10160695065075797 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10160695065075797/10000000000000000 : ℝ)) (X := (107330379935271723523/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (57330379935271723523/50000000000000000000 : ℝ) ≤ (10313100601917929/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (57330379935271723523/50000000000000000000 : ℝ)^16 ≤ (10313100601917929/10000000000000000 : ℝ)^71 := by
      have hnat : (57330379935271723523 : ℕ)^16*10000000000000000^71 ≤ 10313100601917929^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57330379935271723523 50000000000000000000 10313100601917929 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10313100601917929/10000000000000000 : ℝ)) (X := (57330379935271723523/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(160695065075797/5549500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(38101384210533/1387375000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (11099/20000 : ℝ)) (alpha := (160695065075797/5549500000000000 : ℝ)) (beta := (38101384210533/1387375000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11099/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(160695065075797/5549500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(38101384210533/1387375000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (13847/25000 : ℝ) ^ (71/16 : ℝ) ≤ (3633934541206142959/50000000000000000000 : ℝ) := by
    have hpowers : (13847/25000 : ℝ)^71 ≤ (3633934541206142959/50000000000000000000 : ℝ)^16 := by
      have hnat : (13847 : ℕ)^71*50000000000000000000^16 ≤ 3633934541206142959^16*25000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13847 25000 3633934541206142959 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13847/25000 : ℝ)) (X := (3633934541206142959/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (53633934541206142959/50000000000000000000 : ℝ) ≤ (1015936118802203/1000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (53633934541206142959/50000000000000000000 : ℝ)^16 ≤ (1015936118802203/1000000000000000 : ℝ)^71 := by
      have hnat : (53633934541206142959 : ℕ)^16*1000000000000000^71 ≤ 1015936118802203^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53633934541206142959 50000000000000000000 1015936118802203 1000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1015936118802203/1000000000000000 : ℝ)) (X := (53633934541206142959/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (28633934541206142959/25000000000000000000 : ℝ) ≤ (515528272209493/500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (28633934541206142959/25000000000000000000 : ℝ)^16 ≤ (515528272209493/500000000000000 : ℝ)^71 := by
      have hnat : (28633934541206142959 : ℕ)^16*500000000000000^71 ≤ 515528272209493^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28633934541206142959 25000000000000000000 515528272209493 500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (515528272209493/500000000000000 : ℝ)) (X := (28633934541206142959/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(15936118802203/553880000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(15120425616783/553880000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (13847/25000 : ℝ)) (alpha := (15936118802203/553880000000000 : ℝ)) (beta := (15120425616783/553880000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (13847/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(15936118802203/553880000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(15120425616783/553880000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (28277/50000 : ℝ) ^ (71/16 : ℝ) ≤ (7971793050404161507/100000000000000000000 : ℝ) := by
    have hpowers : (28277/50000 : ℝ)^71 ≤ (7971793050404161507/100000000000000000000 : ℝ)^16 := by
      have hnat : (28277 : ℕ)^71*100000000000000000000^16 ≤ 7971793050404161507^16*50000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28277 50000 7971793050404161507 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28277/50000 : ℝ)) (X := (7971793050404161507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (107971793050404161507/100000000000000000000 : ℝ) ≤ (10174347098833433/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (107971793050404161507/100000000000000000000 : ℝ)^16 ≤ (10174347098833433/10000000000000000 : ℝ)^71 := by
      have hnat : (107971793050404161507 : ℕ)^16*10000000000000000^71 ≤ 10174347098833433^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107971793050404161507 100000000000000000000 10174347098833433 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10174347098833433/10000000000000000 : ℝ)) (X := (107971793050404161507/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (57971793050404161507/50000000000000000000 : ℝ) ≤ (516949524765523/500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (57971793050404161507/50000000000000000000 : ℝ)^16 ≤ (516949524765523/500000000000000 : ℝ)^71 := by
      have hnat : (57971793050404161507 : ℕ)^16*500000000000000^71 ≤ 516949524765523^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57971793050404161507 50000000000000000000 516949524765523 500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (516949524765523/500000000000000 : ℝ)) (X := (57971793050404161507/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(174347098833433/5655400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(164643396477027/5655400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (28277/50000 : ℝ)) (alpha := (174347098833433/5655400000000000 : ℝ)) (beta := (164643396477027/5655400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (28277/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(174347098833433/5655400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(164643396477027/5655400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2164599019/10000000000 : ℝ)*X 0 0+(5606872621/10000000000 : ℝ)*X 0 1+(4759250627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((4763904437/10000000000 : ℝ)*X 1 0+(-660155991/5000000000 : ℝ)*X 1 1+(6197149763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((4749232883/10000000000 : ℝ)*X 2 0+(5605759727/10000000000 : ℝ)*X 2 1+(-1089294847/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((5966337783/10000000000 : ℝ)*X 0 0+(999025543/2500000000 : ℝ)*X 0 1+(2609103839/10000000000 : ℝ)*X 0 2+(5966337783/10000000000 : ℝ)*X 1 0+(999025543/2500000000 : ℝ)*X 1 1+(2609103839/10000000000 : ℝ)*X 1 2+(5966337783/10000000000 : ℝ)*X 2 0+(999025543/2500000000 : ℝ)*X 2 1+(2609103839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-468424633/2500000000 : ℝ)*X 0 0+(4937990367/10000000000 : ℝ)*X 0 1+(1413147331/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2302936657/5000000000 : ℝ)*X 1 0+(-631328907/10000000000 : ℝ)*X 1 1+(6740872309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4591099117/10000000000 : ℝ)*X 2 0+(793220673/1250000000 : ℝ)*X 2 1+(-668180211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((5264590391/10000000000 : ℝ)*X 0 0+(5620271271/10000000000 : ℝ)*X 0 1+(1470049817/10000000000 : ℝ)*X 0 2+(5264590391/10000000000 : ℝ)*X 1 0+(5620271271/10000000000 : ℝ)*X 1 1+(1470049817/10000000000 : ℝ)*X 1 2+(5264590391/10000000000 : ℝ)*X 2 0+(5620271271/10000000000 : ℝ)*X 2 1+(1470049817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-76508481/625000000 : ℝ)*X 0 0+(5299068393/10000000000 : ℝ)*X 0 1+(5749439037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4288805997/10000000000 : ℝ)*X 1 0+(-572680801/5000000000 : ℝ)*X 1 1+(1347030717/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((717578761/1250000000 : ℝ)*X 2 0+(2648973987/5000000000 : ℝ)*X 2 1+(-619756329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((7133131087/10000000000 : ℝ)*X 0 0+(3573752917/10000000000 : ℝ)*X 0 1+(1483121113/10000000000 : ℝ)*X 0 2+(7133131087/10000000000 : ℝ)*X 1 0+(3573752917/10000000000 : ℝ)*X 1 1+(1483121113/10000000000 : ℝ)*X 1 2+(7133131087/10000000000 : ℝ)*X 2 0+(3573752917/10000000000 : ℝ)*X 2 1+(1483121113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-1207092409/10000000000 : ℝ)*X 0 0+(3104766097/5000000000 : ℝ)*X 0 1+(2413958221/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((2886226271/5000000000 : ℝ)*X 1 0+(-59764773/1000000000 : ℝ)*X 1 1+(5649478129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4224265149/10000000000 : ℝ)*X 2 0+(6379448759/10000000000 : ℝ)*X 2 1+(-1780025833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((7246932127/10000000000 : ℝ)*X 0 0+(339038609/1250000000 : ℝ)*X 0 1+(2312355683/10000000000 : ℝ)*X 0 2+(7246932127/10000000000 : ℝ)*X 1 0+(339038609/1250000000 : ℝ)*X 1 1+(2312355683/10000000000 : ℝ)*X 1 2+(7246932127/10000000000 : ℝ)*X 2 0+(339038609/1250000000 : ℝ)*X 2 1+(2312355683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((35487/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35487/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2238454861035832915992557580837/543228927410125000000000000000000000 : ℝ) := by norm_num
    linear_combination (246557472203/500000000000 : ℝ)*(base49) + (5100676505563/1000000000000 : ℝ)*(major_s3_0) + (5100676505563/1000000000000 : ℝ)*(major_s3_1) + (5100676505563/1000000000000 : ℝ)*(major_s3_2) + (22628107/1000000000000 : ℝ)*(sp_s3_0) + (6111277/200000000000 : ℝ)*(sp_s3_1) + (2874193/1000000000000 : ℝ)*(sp_s3_6) + (7097738788861/1000000000000 : ℝ)*(sp_s3_7) + (7097737878783/1000000000000 : ℝ)*(sp_s3_8) + (3548838572833/500000000000 : ℝ)*(sp_s3_9) + (24246719337/7812500000 : ℝ)*(sp_s3_13) + (3635639/500000000000 : ℝ)*(sp_s3_14) + (126539/500000000000 : ℝ)*(sp_s3_22) + (4577129/50000000000 : ℝ)*(sp_s3_23) + (3103582949329/1000000000000 : ℝ)*(f.failure) + (3548884344123/500000000000 : ℝ)*(f.sum) + (862595124692346359/39155161900000000000000000000000 : ℝ)*base63 + (1574175418438399/5655400000000000000000000000 : ℝ)*base64 + (158879500212493/553880000000000000000000000 : ℝ)*base66 + (1144728070168341/5655400000000000000000000000 : ℝ)*base68 + (4923221038564428911/313846423000000000000000000000000 : ℝ)*base70 + (763875394572267/2774750000000000000000000000 : ℝ)*base72 + (142976313250867/553880000000000000000000000 : ℝ)*base74 + (1636936149270489/5549500000000000000000000000 : ℝ)*base76 + (1826536345284829571/153687853000000000000000000000000 : ℝ)*base78 + (5623/25000000000000000 : ℝ)*base87 + (5623/25000000000000000 : ℝ)*base89 + (5623/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36397/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7082707734144240821432804708877/543228927410125000000000000000000000 : ℝ) := by norm_num
    linear_combination (2794387/1000000000000 : ℝ)*(base39) + (80754568379/200000000000 : ℝ)*(base49) + (1341639/1000000000000 : ℝ)*(base60) + (1224994119379/250000000000 : ℝ)*(major_s3_0) + (1224994119379/250000000000 : ℝ)*(major_s3_1) + (1224994119379/250000000000 : ℝ)*(major_s3_2) + (1758427/500000000000 : ℝ)*(sp_s3_2) + (32108641/1000000000000 : ℝ)*(sp_s3_7) + (78817663/1000000000000 : ℝ)*(sp_s3_8) + (6818452486461/1000000000000 : ℝ)*(sp_s3_14) + (6818405777439/1000000000000 : ℝ)*(sp_s3_15) + (852310134781/125000000000 : ℝ)*(sp_s3_16) + (2981396184029/1000000000000 : ℝ)*(sp_s3_20) + (67829841/1000000000000 : ℝ)*(sp_s3_27) + (2981464013871/1000000000000 : ℝ)*(f.failure) + (3409242297551/500000000000 : ℝ)*(f.sum) + (2927304630272720121/4894395237500000000000000000000 : ℝ)*base63 + (77599743649823/353462500000000000000000000 : ℝ)*base64 + (11213578802043/17308750000000000000000000 : ℝ)*base66 + (16443005968627/88365625000000000000000000 : ℝ)*base69 + (15557925697258645787/78461605750000000000000000000000 : ℝ)*base71 + (487254501559447/1387375000000000000000000000 : ℝ)*base72 + (2978265783009/27694000000000000000000000 : ℝ)*base75 + (507641239863499/2774750000000000000000000000 : ℝ)*base76 + (7637999371831440643/38421963250000000000000000000000 : ℝ)*base78 + (17777/25000000000000000 : ℝ)*base87 + (17777/25000000000000000 : ℝ)*base89 + (17777/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18001/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18001/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2209921684254406442470781264031/217291570964050000000000000000000000 : ℝ) := by norm_num
    linear_combination (11154482501/100000000000 : ℝ)*(base40) + (9766969523/25000000000 : ℝ)*(base49) + (5152141/1000000000000 : ℝ)*(base59) + (1171627864941/250000000000 : ℝ)*(major_s3_0) + (1171627864941/250000000000 : ℝ)*(major_s3_1) + (1171627864941/250000000000 : ℝ)*(major_s3_2) + (28499011/1000000000000 : ℝ)*(sp_s3_0) + (18049373/500000000000 : ℝ)*(sp_s3_2) + (27011397/1000000000000 : ℝ)*(sp_s3_9) + (20264241/200000000000 : ℝ)*(sp_s3_20) + (1304282600201/200000000000 : ℝ)*(sp_s3_21) + (407590093751/62500000000 : ℝ)*(sp_s3_22) + (6521378389873/1000000000000 : ℝ)*(sp_s3_23) + (1425738354099/500000000000 : ℝ)*(sp_s3_27) + (2851578029403/1000000000000 : ℝ)*(f.failure) + (407590093751/62500000000 : ℝ)*(f.sum) + (6009369347683673481/19577580950000000000000000000000 : ℝ)*base63 + (97839146731763/1413850000000000000000000000 : ℝ)*base64 + (1370076784123/27694000000000000000000000 : ℝ)*base67 + (78565111375381/176731250000000000000000000 : ℝ)*base69 + (14240459667732542463/19615401437500000000000000000000 : ℝ)*base70 + (2007673171517499/2774750000000000000000000000 : ℝ)*base73 + (7829202761431/17308750000000000000000000 : ℝ)*base75 + (74497401462887/346843750000000000000000000 : ℝ)*base76 + (13591258016708244803/38421963250000000000000000000000 : ℝ)*base79 + (18939/25000000000000000 : ℝ)*base86 + (18939/25000000000000000 : ℝ)*base88 + (18939/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((11099/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11099/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13847/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13847/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28277/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28277/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35487/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35487/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36397/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18001/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18001/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311055_s3 p hpa hpb X hX hprev2

#print axioms solution
