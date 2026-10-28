-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301062_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:39:04.159181+00:00
-- url     : https://prove2.me/submissions/a66bbc1e-6c0b-4a26-86e1-21b3b03807b8

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
theorem collision_support_c301062_s5_s5_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-229945189/1000000000 : ℝ)*x 0 + (4869758209/10000000000 : ℝ)*x 1 + (-2842230473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (229945189/1000000000 : ℝ)^65 ≤ (14229024539457/100000000000000 : ℝ)^49 := by
    have hnat : (229945189 : ℕ)^65*100000000000000^49 ≤ 14229024539457^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229945189 1000000000 14229024539457 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4869758209/10000000000 : ℝ)^65 ≤ (38500732989227/100000000000000 : ℝ)^49 := by
    have hnat : (4869758209 : ℕ)^65*100000000000000^49 ≤ 38500732989227^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4869758209 10000000000 38500732989227 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2842230473/5000000000 : ℝ)^65 ≤ (378161939603/800000000000 : ℝ)^49 := by
    have hnat : (2842230473 : ℕ)^65*800000000000^49 ≤ 378161939603^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842230473 5000000000 378161939603 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-229945189/1000000000 : ℝ), (4869758209/10000000000 : ℝ), (-2842230473/5000000000 : ℝ)] ![(14229024539457/100000000000000 : ℝ), (38500732989227/100000000000000 : ℝ), (378161939603/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-229945189/1000000000 : ℝ)|^65 ≤ (14229024539457/100000000000000 : ℝ)^49
        have hw : |(-229945189/1000000000 : ℝ)|=(229945189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4869758209/10000000000 : ℝ)|^65 ≤ (38500732989227/100000000000000 : ℝ)^49
        have hw : |(4869758209/10000000000 : ℝ)|=(4869758209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2842230473/5000000000 : ℝ)|^65 ≤ (378161939603/800000000000 : ℝ)^49
        have hw : |(-2842230473/5000000000 : ℝ)|=(2842230473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4867787797/10000000000 : ℝ)*x 0 + (-576043669/2500000000 : ℝ)*x 1 + (-177588079/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4867787797/10000000000 : ℝ)^65 ≤ (38480069330221/100000000000000 : ℝ)^49 := by
    have hnat : (4867787797 : ℕ)^65*100000000000000^49 ≤ 38480069330221^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867787797 10000000000 38480069330221 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576043669/2500000000 : ℝ)^65 ≤ (570712196147/4000000000000 : ℝ)^49 := by
    have hnat : (576043669 : ℕ)^65*4000000000000^49 ≤ 570712196147^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576043669 2500000000 570712196147 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177588079/312500000 : ℝ)^65 ≤ (47252125753127/100000000000000 : ℝ)^49 := by
    have hnat : (177588079 : ℕ)^65*100000000000000^49 ≤ 47252125753127^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177588079 312500000 47252125753127 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4867787797/10000000000 : ℝ), (-576043669/2500000000 : ℝ), (-177588079/312500000 : ℝ)] ![(38480069330221/100000000000000 : ℝ), (570712196147/4000000000000 : ℝ), (47252125753127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4867787797/10000000000 : ℝ)|^65 ≤ (38480069330221/100000000000000 : ℝ)^49
        have hw : |(4867787797/10000000000 : ℝ)|=(4867787797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-576043669/2500000000 : ℝ)|^65 ≤ (570712196147/4000000000000 : ℝ)^49
        have hw : |(-576043669/2500000000 : ℝ)|=(576043669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-177588079/312500000 : ℝ)|^65 ≤ (47252125753127/100000000000000 : ℝ)^49
        have hw : |(-177588079/312500000 : ℝ)|=(177588079/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5459639059/10000000000 : ℝ)*x 0 + (5451209921/10000000000 : ℝ)*x 1 + (-1825874703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5459639059/10000000000 : ℝ)^65 ≤ (11201596345221/25000000000000 : ℝ)^49 := by
    have hnat : (5459639059 : ℕ)^65*25000000000000^49 ≤ 11201596345221^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459639059 10000000000 11201596345221 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451209921/10000000000 : ℝ)^65 ≤ (44714643657081/100000000000000 : ℝ)^49 := by
    have hnat : (5451209921 : ℕ)^65*100000000000000^49 ≤ 44714643657081^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451209921 10000000000 44714643657081 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1825874703/10000000000 : ℝ)^65 ≤ (1047897093641/10000000000000 : ℝ)^49 := by
    have hnat : (1825874703 : ℕ)^65*10000000000000^49 ≤ 1047897093641^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825874703 10000000000 1047897093641 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5459639059/10000000000 : ℝ), (5451209921/10000000000 : ℝ), (-1825874703/10000000000 : ℝ)] ![(11201596345221/25000000000000 : ℝ), (44714643657081/100000000000000 : ℝ), (1047897093641/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5459639059/10000000000 : ℝ)|^65 ≤ (11201596345221/25000000000000 : ℝ)^49
        have hw : |(5459639059/10000000000 : ℝ)|=(5459639059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451209921/10000000000 : ℝ)|^65 ≤ (44714643657081/100000000000000 : ℝ)^49
        have hw : |(5451209921/10000000000 : ℝ)|=(5451209921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1825874703/10000000000 : ℝ)|^65 ≤ (1047897093641/10000000000000 : ℝ)^49
        have hw : |(-1825874703/10000000000 : ℝ)|=(1825874703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010201671/10000000000 : ℝ)*x 0 + (1103130101/2500000000 : ℝ)*x 1 + (-3156006201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010201671/10000000000 : ℝ)^65 ≤ (11904907884391/100000000000000 : ℝ)^49 := by
    have hnat : (2010201671 : ℕ)^65*100000000000000^49 ≤ 11904907884391^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010201671 10000000000 11904907884391 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103130101/2500000000 : ℝ)^65 ≤ (4222562426781/12500000000000 : ℝ)^49 := by
    have hnat : (1103130101 : ℕ)^65*12500000000000^49 ≤ 4222562426781^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103130101 2500000000 4222562426781 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3156006201/5000000000 : ℝ)^65 ≤ (54314592694993/100000000000000 : ℝ)^49 := by
    have hnat : (3156006201 : ℕ)^65*100000000000000^49 ≤ 54314592694993^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3156006201 5000000000 54314592694993 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010201671/10000000000 : ℝ), (1103130101/2500000000 : ℝ), (-3156006201/5000000000 : ℝ)] ![(11904907884391/100000000000000 : ℝ), (4222562426781/12500000000000 : ℝ), (54314592694993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010201671/10000000000 : ℝ)|^65 ≤ (11904907884391/100000000000000 : ℝ)^49
        have hw : |(-2010201671/10000000000 : ℝ)|=(2010201671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1103130101/2500000000 : ℝ)|^65 ≤ (4222562426781/12500000000000 : ℝ)^49
        have hw : |(1103130101/2500000000 : ℝ)|=(1103130101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3156006201/5000000000 : ℝ)|^65 ≤ (54314592694993/100000000000000 : ℝ)^49
        have hw : |(-3156006201/5000000000 : ℝ)|=(3156006201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1202602801/2500000000 : ℝ)*x 0 + (-338580637/2000000000 : ℝ)*x 1 + (-3082440857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1202602801/2500000000 : ℝ)^65 ≤ (37879563193687/100000000000000 : ℝ)^49 := by
    have hnat : (1202602801 : ℕ)^65*100000000000000^49 ≤ 37879563193687^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202602801 2500000000 37879563193687 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338580637/2000000000 : ℝ)^65 ≤ (9478877192369/100000000000000 : ℝ)^49 := by
    have hnat : (338580637 : ℕ)^65*100000000000000^49 ≤ 9478877192369^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338580637 2000000000 9478877192369 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3082440857/5000000000 : ℝ)^65 ≤ (52641559604091/100000000000000 : ℝ)^49 := by
    have hnat : (3082440857 : ℕ)^65*100000000000000^49 ≤ 52641559604091^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3082440857 5000000000 52641559604091 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1202602801/2500000000 : ℝ), (-338580637/2000000000 : ℝ), (-3082440857/5000000000 : ℝ)] ![(37879563193687/100000000000000 : ℝ), (9478877192369/100000000000000 : ℝ), (52641559604091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1202602801/2500000000 : ℝ)|^65 ≤ (37879563193687/100000000000000 : ℝ)^49
        have hw : |(1202602801/2500000000 : ℝ)|=(1202602801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-338580637/2000000000 : ℝ)|^65 ≤ (9478877192369/100000000000000 : ℝ)^49
        have hw : |(-338580637/2000000000 : ℝ)|=(338580637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3082440857/5000000000 : ℝ)|^65 ≤ (52641559604091/100000000000000 : ℝ)^49
        have hw : |(-3082440857/5000000000 : ℝ)|=(3082440857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2446175723/5000000000 : ℝ)*x 0 + (589698097/1000000000 : ℝ)*x 1 + (19755421/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2446175723/5000000000 : ℝ)^65 ≤ (9684465656023/25000000000000 : ℝ)^49 := by
    have hnat : (2446175723 : ℕ)^65*25000000000000^49 ≤ 9684465656023^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2446175723 5000000000 9684465656023 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (589698097/1000000000 : ℝ)^65 ≤ (24814373492509/50000000000000 : ℝ)^49 := by
    have hnat : (589698097 : ℕ)^65*50000000000000^49 ≤ 24814373492509^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589698097 1000000000 24814373492509 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19755421/100000000 : ℝ)^65 ≤ (1163339038263/10000000000000 : ℝ)^49 := by
    have hnat : (19755421 : ℕ)^65*10000000000000^49 ≤ 1163339038263^49*100000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19755421 100000000 1163339038263 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2446175723/5000000000 : ℝ), (589698097/1000000000 : ℝ), (19755421/100000000 : ℝ)] ![(9684465656023/25000000000000 : ℝ), (24814373492509/50000000000000 : ℝ), (1163339038263/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2446175723/5000000000 : ℝ)|^65 ≤ (9684465656023/25000000000000 : ℝ)^49
        have hw : |(2446175723/5000000000 : ℝ)|=(2446175723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(589698097/1000000000 : ℝ)|^65 ≤ (24814373492509/50000000000000 : ℝ)^49
        have hw : |(589698097/1000000000 : ℝ)|=(589698097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19755421/100000000 : ℝ)|^65 ≤ (1163339038263/10000000000000 : ℝ)^49
        have hw : |(19755421/100000000 : ℝ)|=(19755421/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (161895869/312500000 : ℝ)*x 0 + (759791581/1250000000 : ℝ)*x 1 + (-1279990817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161895869/312500000 : ℝ)^65 ≤ (66871941281/160000000000 : ℝ)^49 := by
    have hnat : (161895869 : ℕ)^65*160000000000^49 ≤ 66871941281^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161895869 312500000 66871941281 160000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (759791581/1250000000 : ℝ)^65 ≤ (51663458128431/100000000000000 : ℝ)^49 := by
    have hnat : (759791581 : ℕ)^65*100000000000000^49 ≤ 51663458128431^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759791581 1250000000 51663458128431 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279990817/10000000000 : ℝ)^65 ≤ (163539463987/2500000000000 : ℝ)^49 := by
    have hnat : (1279990817 : ℕ)^65*2500000000000^49 ≤ 163539463987^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279990817 10000000000 163539463987 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161895869/312500000 : ℝ), (759791581/1250000000 : ℝ), (-1279990817/10000000000 : ℝ)] ![(66871941281/160000000000 : ℝ), (51663458128431/100000000000000 : ℝ), (163539463987/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161895869/312500000 : ℝ)|^65 ≤ (66871941281/160000000000 : ℝ)^49
        have hw : |(161895869/312500000 : ℝ)|=(161895869/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(759791581/1250000000 : ℝ)|^65 ≤ (51663458128431/100000000000000 : ℝ)^49
        have hw : |(759791581/1250000000 : ℝ)|=(759791581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1279990817/10000000000 : ℝ)|^65 ≤ (163539463987/2500000000000 : ℝ)^49
        have hw : |(-1279990817/10000000000 : ℝ)|=(1279990817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-811657181/5000000000 : ℝ)*x 0 + (2371216483/5000000000 : ℝ)*x 1 + (-1568110487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811657181/5000000000 : ℝ)^65 ≤ (8965508336103/100000000000000 : ℝ)^49 := by
    have hnat : (811657181 : ℕ)^65*100000000000000^49 ≤ 8965508336103^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811657181 5000000000 8965508336103 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2371216483/5000000000 : ℝ)^65 ≤ (37171122366521/100000000000000 : ℝ)^49 := by
    have hnat : (2371216483 : ℕ)^65*100000000000000^49 ≤ 37171122366521^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371216483 5000000000 37171122366521 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1568110487/2500000000 : ℝ)^65 ≤ (26931684640099/50000000000000 : ℝ)^49 := by
    have hnat : (1568110487 : ℕ)^65*50000000000000^49 ≤ 26931684640099^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568110487 2500000000 26931684640099 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-811657181/5000000000 : ℝ), (2371216483/5000000000 : ℝ), (-1568110487/2500000000 : ℝ)] ![(8965508336103/100000000000000 : ℝ), (37171122366521/100000000000000 : ℝ), (26931684640099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-811657181/5000000000 : ℝ)|^65 ≤ (8965508336103/100000000000000 : ℝ)^49
        have hw : |(-811657181/5000000000 : ℝ)|=(811657181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2371216483/5000000000 : ℝ)|^65 ≤ (37171122366521/100000000000000 : ℝ)^49
        have hw : |(2371216483/5000000000 : ℝ)|=(2371216483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1568110487/2500000000 : ℝ)|^65 ≤ (26931684640099/50000000000000 : ℝ)^49
        have hw : |(-1568110487/2500000000 : ℝ)|=(1568110487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (179567643/400000000 : ℝ)*x 0 + (-1043830239/5000000000 : ℝ)*x 1 + (-3094787913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179567643/400000000 : ℝ)^65 ≤ (34561320273223/100000000000000 : ℝ)^49 := by
    have hnat : (179567643 : ℕ)^65*100000000000000^49 ≤ 34561320273223^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179567643 400000000 34561320273223 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043830239/5000000000 : ℝ)^65 ≤ (2503444604489/20000000000000 : ℝ)^49 := by
    have hnat : (1043830239 : ℕ)^65*20000000000000^49 ≤ 2503444604489^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043830239 5000000000 2503444604489 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3094787913/5000000000 : ℝ)^65 ≤ (10584291335897/20000000000000 : ℝ)^49 := by
    have hnat : (3094787913 : ℕ)^65*20000000000000^49 ≤ 10584291335897^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3094787913 5000000000 10584291335897 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(179567643/400000000 : ℝ), (-1043830239/5000000000 : ℝ), (-3094787913/5000000000 : ℝ)] ![(34561320273223/100000000000000 : ℝ), (2503444604489/20000000000000 : ℝ), (10584291335897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(179567643/400000000 : ℝ)|^65 ≤ (34561320273223/100000000000000 : ℝ)^49
        have hw : |(179567643/400000000 : ℝ)|=(179567643/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1043830239/5000000000 : ℝ)|^65 ≤ (2503444604489/20000000000000 : ℝ)^49
        have hw : |(-1043830239/5000000000 : ℝ)|=(1043830239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3094787913/5000000000 : ℝ)|^65 ≤ (10584291335897/20000000000000 : ℝ)^49
        have hw : |(-3094787913/5000000000 : ℝ)|=(3094787913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5808688263/10000000000 : ℝ)*x 0 + (4975536547/10000000000 : ℝ)*x 1 + (497310259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5808688263/10000000000 : ℝ)^65 ≤ (48645462552949/100000000000000 : ℝ)^49 := by
    have hnat : (5808688263 : ℕ)^65*100000000000000^49 ≤ 48645462552949^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5808688263 10000000000 48645462552949 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4975536547/10000000000 : ℝ)^65 ≤ (19807008075069/50000000000000 : ℝ)^49 := by
    have hnat : (4975536547 : ℕ)^65*50000000000000^49 ≤ 19807008075069^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4975536547 10000000000 19807008075069 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497310259/2500000000 : ℝ)^65 ≤ (11740521284607/100000000000000 : ℝ)^49 := by
    have hnat : (497310259 : ℕ)^65*100000000000000^49 ≤ 11740521284607^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497310259 2500000000 11740521284607 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5808688263/10000000000 : ℝ), (4975536547/10000000000 : ℝ), (497310259/2500000000 : ℝ)] ![(48645462552949/100000000000000 : ℝ), (19807008075069/50000000000000 : ℝ), (11740521284607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5808688263/10000000000 : ℝ)|^65 ≤ (48645462552949/100000000000000 : ℝ)^49
        have hw : |(5808688263/10000000000 : ℝ)|=(5808688263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4975536547/10000000000 : ℝ)|^65 ≤ (19807008075069/50000000000000 : ℝ)^49
        have hw : |(4975536547/10000000000 : ℝ)|=(4975536547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(497310259/2500000000 : ℝ)|^65 ≤ (11740521284607/100000000000000 : ℝ)^49
        have hw : |(497310259/2500000000 : ℝ)|=(497310259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3118689517/5000000000 : ℝ)*x 0 + (5010003513/10000000000 : ℝ)*x 1 + (-1282298521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3118689517/5000000000 : ℝ)^65 ≤ (53464321307453/100000000000000 : ℝ)^49 := by
    have hnat : (3118689517 : ℕ)^65*100000000000000^49 ≤ 53464321307453^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118689517 5000000000 53464321307453 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5010003513/10000000000 : ℝ)^65 ≤ (9994612650951/25000000000000 : ℝ)^49 := by
    have hnat : (5010003513 : ℕ)^65*25000000000000^49 ≤ 9994612650951^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010003513 10000000000 9994612650951 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282298521/10000000000 : ℝ)^65 ≤ (819653509171/12500000000000 : ℝ)^49 := by
    have hnat : (1282298521 : ℕ)^65*12500000000000^49 ≤ 819653509171^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282298521 10000000000 819653509171 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3118689517/5000000000 : ℝ), (5010003513/10000000000 : ℝ), (-1282298521/10000000000 : ℝ)] ![(53464321307453/100000000000000 : ℝ), (9994612650951/25000000000000 : ℝ), (819653509171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3118689517/5000000000 : ℝ)|^65 ≤ (53464321307453/100000000000000 : ℝ)^49
        have hw : |(3118689517/5000000000 : ℝ)|=(3118689517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5010003513/10000000000 : ℝ)|^65 ≤ (9994612650951/25000000000000 : ℝ)^49
        have hw : |(5010003513/10000000000 : ℝ)|=(5010003513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1282298521/10000000000 : ℝ)|^65 ≤ (819653509171/12500000000000 : ℝ)^49
        have hw : |(-1282298521/10000000000 : ℝ)|=(1282298521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1407711383/10000000000 : ℝ)*x 0 + (32699483/62500000 : ℝ)*x 1 + (-5951153847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1407711383/10000000000 : ℝ)^65 ≤ (3710626642831/50000000000000 : ℝ)^49 := by
    have hnat : (1407711383 : ℕ)^65*50000000000000^49 ≤ 3710626642831^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407711383 10000000000 3710626642831 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32699483/62500000 : ℝ)^65 ≤ (21172153524207/50000000000000 : ℝ)^49 := by
    have hnat : (32699483 : ℕ)^65*50000000000000^49 ≤ 21172153524207^49*62500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32699483 62500000 21172153524207 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5951153847/10000000000 : ℝ)^65 ≤ (12558609911373/25000000000000 : ℝ)^49 := by
    have hnat : (5951153847 : ℕ)^65*25000000000000^49 ≤ 12558609911373^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5951153847 10000000000 12558609911373 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1407711383/10000000000 : ℝ), (32699483/62500000 : ℝ), (-5951153847/10000000000 : ℝ)] ![(3710626642831/50000000000000 : ℝ), (21172153524207/50000000000000 : ℝ), (12558609911373/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1407711383/10000000000 : ℝ)|^65 ≤ (3710626642831/50000000000000 : ℝ)^49
        have hw : |(-1407711383/10000000000 : ℝ)|=(1407711383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32699483/62500000 : ℝ)|^65 ≤ (21172153524207/50000000000000 : ℝ)^49
        have hw : |(32699483/62500000 : ℝ)|=(32699483/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5951153847/10000000000 : ℝ)|^65 ≤ (12558609911373/25000000000000 : ℝ)^49
        have hw : |(-5951153847/10000000000 : ℝ)|=(5951153847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2893396943/5000000000 : ℝ)*x 0 + (-1969307933/10000000000 : ℝ)*x 1 + (-626657189/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2893396943/5000000000 : ℝ)^65 ≤ (48402384041571/100000000000000 : ℝ)^49 := by
    have hnat : (2893396943 : ℕ)^65*100000000000000^49 ≤ 48402384041571^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2893396943 5000000000 48402384041571 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1969307933/10000000000 : ℝ)^65 ≤ (2316943395027/20000000000000 : ℝ)^49 := by
    have hnat : (1969307933 : ℕ)^65*20000000000000^49 ≤ 2316943395027^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969307933 10000000000 2316943395027 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626657189/1250000000 : ℝ)^65 ≤ (160051595891/400000000000 : ℝ)^49 := by
    have hnat : (626657189 : ℕ)^65*400000000000^49 ≤ 160051595891^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626657189 1250000000 160051595891 400000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2893396943/5000000000 : ℝ), (-1969307933/10000000000 : ℝ), (-626657189/1250000000 : ℝ)] ![(48402384041571/100000000000000 : ℝ), (2316943395027/20000000000000 : ℝ), (160051595891/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2893396943/5000000000 : ℝ)|^65 ≤ (48402384041571/100000000000000 : ℝ)^49
        have hw : |(2893396943/5000000000 : ℝ)|=(2893396943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1969307933/10000000000 : ℝ)|^65 ≤ (2316943395027/20000000000000 : ℝ)^49
        have hw : |(-1969307933/10000000000 : ℝ)|=(1969307933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-626657189/1250000000 : ℝ)|^65 ≤ (160051595891/400000000000 : ℝ)^49
        have hw : |(-626657189/1250000000 : ℝ)|=(626657189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (14629713/31250000 : ℝ)*x 0 + (5465019257/10000000000 : ℝ)*x 1 + (2813554391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14629713/31250000 : ℝ)^65 ≤ (18269499822709/50000000000000 : ℝ)^49 := by
    have hnat : (14629713 : ℕ)^65*50000000000000^49 ≤ 18269499822709^49*31250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14629713 31250000 18269499822709 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465019257/10000000000 : ℝ)^65 ≤ (22432483499647/50000000000000 : ℝ)^49 := by
    have hnat : (5465019257 : ℕ)^65*50000000000000^49 ≤ 22432483499647^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465019257 10000000000 22432483499647 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2813554391/10000000000 : ℝ)^65 ≤ (18596033340629/100000000000000 : ℝ)^49 := by
    have hnat : (2813554391 : ℕ)^65*100000000000000^49 ≤ 18596033340629^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813554391 10000000000 18596033340629 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(14629713/31250000 : ℝ), (5465019257/10000000000 : ℝ), (2813554391/10000000000 : ℝ)] ![(18269499822709/50000000000000 : ℝ), (22432483499647/50000000000000 : ℝ), (18596033340629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(14629713/31250000 : ℝ)|^65 ≤ (18269499822709/50000000000000 : ℝ)^49
        have hw : |(14629713/31250000 : ℝ)|=(14629713/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465019257/10000000000 : ℝ)|^65 ≤ (22432483499647/50000000000000 : ℝ)^49
        have hw : |(5465019257/10000000000 : ℝ)|=(5465019257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2813554391/10000000000 : ℝ)|^65 ≤ (18596033340629/100000000000000 : ℝ)^49
        have hw : |(2813554391/10000000000 : ℝ)|=(2813554391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s5_s5_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3162932451/5000000000 : ℝ)*x 0 + (4778212913/10000000000 : ℝ)*x 1 + (-92962567/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3162932451/5000000000 : ℝ)^65 ≤ (13618192996533/25000000000000 : ℝ)^49 := by
    have hnat : (3162932451 : ℕ)^65*25000000000000^49 ≤ 13618192996533^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3162932451 5000000000 13618192996533 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4778212913/10000000000 : ℝ)^65 ≤ (37543595683383/100000000000000 : ℝ)^49 := by
    have hnat : (4778212913 : ℕ)^65*100000000000000^49 ≤ 37543595683383^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778212913 10000000000 37543595683383 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92962567/625000000 : ℝ)^65 ≤ (997954040263/12500000000000 : ℝ)^49 := by
    have hnat : (92962567 : ℕ)^65*12500000000000^49 ≤ 997954040263^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92962567 625000000 997954040263 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3162932451/5000000000 : ℝ), (4778212913/10000000000 : ℝ), (-92962567/625000000 : ℝ)] ![(13618192996533/25000000000000 : ℝ), (37543595683383/100000000000000 : ℝ), (997954040263/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3162932451/5000000000 : ℝ)|^65 ≤ (13618192996533/25000000000000 : ℝ)^49
        have hw : |(3162932451/5000000000 : ℝ)|=(3162932451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4778212913/10000000000 : ℝ)|^65 ≤ (37543595683383/100000000000000 : ℝ)^49
        have hw : |(4778212913/10000000000 : ℝ)|=(4778212913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-92962567/625000000 : ℝ)|^65 ≤ (997954040263/12500000000000 : ℝ)^49
        have hw : |(-92962567/625000000 : ℝ)|=(92962567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301062_s5 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev4 : (0 : ℝ) ≤ ((29189/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29189/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14691/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14691/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5079/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5079/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((34121/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34121/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34301/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34301/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5293/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5293/25000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (29189/50000 : ℝ) ^ (129/32 : ℝ) ≤ (11420684566160791273/100000000000000000000 : ℝ) := by
    have hpowers : (29189/50000 : ℝ)^129 ≤ (11420684566160791273/100000000000000000000 : ℝ)^32 := by
      have hnat : (29189 : ℕ)^129*100000000000000000000^32 ≤ 11420684566160791273^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29189 50000 11420684566160791273 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29189/50000 : ℝ)) (X := (11420684566160791273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0a : (111420684566160791273/100000000000000000000 : ℝ) ≤ (1283986476497647/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (111420684566160791273/100000000000000000000 : ℝ)^32 ≤ (1283986476497647/1250000000000000 : ℝ)^129 := by
      have hnat : (111420684566160791273 : ℕ)^32*1250000000000000^129 ≤ 1283986476497647^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111420684566160791273 100000000000000000000 1283986476497647 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1283986476497647/1250000000000000 : ℝ)) (X := (111420684566160791273/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0b : (61420684566160791273/50000000000000000000 : ℝ) ≤ (5261784022255133/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (61420684566160791273/50000000000000000000 : ℝ)^32 ≤ (5261784022255133/5000000000000000 : ℝ)^129 := by
      have hnat : (61420684566160791273 : ℕ)^32*5000000000000000^129 ≤ 5261784022255133^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61420684566160791273 50000000000000000000 5261784022255133 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5261784022255133/5000000000000000 : ℝ)) (X := (61420684566160791273/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(33986476497647/729725000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(25167623252909/583780000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (29189/50000 : ℝ)) (alpha := (33986476497647/729725000000000 : ℝ)) (beta := (25167623252909/583780000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (29189/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(33986476497647/729725000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(25167623252909/583780000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (14691/25000 : ℝ) ^ (129/32 : ℝ) ≤ (2932041673003918897/25000000000000000000 : ℝ) := by
    have hpowers : (14691/25000 : ℝ)^129 ≤ (2932041673003918897/25000000000000000000 : ℝ)^32 := by
      have hnat : (14691 : ℕ)^129*25000000000000000000^32 ≤ 2932041673003918897^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14691 25000 2932041673003918897 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14691/25000 : ℝ)) (X := (2932041673003918897/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1a : (27932041673003918897/25000000000000000000 : ℝ) ≤ (256972907489301/250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (27932041673003918897/25000000000000000000 : ℝ)^32 ≤ (256972907489301/250000000000000 : ℝ)^129 := by
      have hnat : (27932041673003918897 : ℕ)^32*250000000000000^129 ≤ 256972907489301^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27932041673003918897 25000000000000000000 256972907489301 250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (256972907489301/250000000000000 : ℝ)) (X := (27932041673003918897/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1b : (15432041673003918897/12500000000000000000 : ℝ) ≤ (2572415063983/2441406250000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (15432041673003918897/12500000000000000000 : ℝ)^32 ≤ (2572415063983/2441406250000 : ℝ)^129 := by
      have hnat : (15432041673003918897 : ℕ)^32*2441406250000^129 ≤ 2572415063983^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15432041673003918897 12500000000000000000 2572415063983 2441406250000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2572415063983/2441406250000 : ℝ)) (X := (15432041673003918897/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(6972907489301/146910000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(32211975312791/734550000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (14691/25000 : ℝ)) (alpha := (6972907489301/146910000000000 : ℝ)) (beta := (32211975312791/734550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (14691/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(6972907489301/146910000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(32211975312791/734550000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (5079/12500 : ℝ) ^ (129/32 : ℝ) ≤ (132501237640988899/5000000000000000000 : ℝ) := by
    have hpowers : (5079/12500 : ℝ)^129 ≤ (132501237640988899/5000000000000000000 : ℝ)^32 := by
      have hnat : (5079 : ℕ)^129*5000000000000000000^32 ≤ 132501237640988899^32*12500^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5079 12500 132501237640988899 5000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5079/12500 : ℝ)) (X := (132501237640988899/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2a : (5132501237640988899/5000000000000000000 : ℝ) ≤ (5032546023361999/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (5132501237640988899/5000000000000000000 : ℝ)^32 ≤ (5032546023361999/5000000000000000 : ℝ)^129 := by
      have hnat : (5132501237640988899 : ℕ)^32*5000000000000000^129 ≤ 5032546023361999^129*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5132501237640988899 5000000000000000000 5032546023361999 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5032546023361999/5000000000000000 : ℝ)) (X := (5132501237640988899/5000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2b : (2632501237640988899/2500000000000000000 : ℝ) ≤ (1266116564363649/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2632501237640988899/2500000000000000000 : ℝ)^32 ≤ (1266116564363649/1250000000000000 : ℝ)^129 := by
      have hnat : (2632501237640988899 : ℕ)^32*1250000000000000^129 ≤ 1266116564363649^129*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2632501237640988899 2500000000000000000 1266116564363649 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1266116564363649/1250000000000000 : ℝ)) (X := (2632501237640988899/2500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(32546023361999/2031600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(31920234092597/2031600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (5079/12500 : ℝ)) (alpha := (32546023361999/2031600000000000 : ℝ)) (beta := (31920234092597/2031600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (5079/12500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(32546023361999/2031600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(31920234092597/2031600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-229945189/1000000000 : ℝ)*X 0 0+(4869758209/10000000000 : ℝ)*X 0 1+(-2842230473/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((4867787797/10000000000 : ℝ)*X 1 0+(-576043669/2500000000 : ℝ)*X 1 1+(-177588079/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((5459639059/10000000000 : ℝ)*X 0 0+(5451209921/10000000000 : ℝ)*X 0 1+(-1825874703/10000000000 : ℝ)*X 0 2+(5459639059/10000000000 : ℝ)*X 1 0+(5451209921/10000000000 : ℝ)*X 1 1+(-1825874703/10000000000 : ℝ)*X 1 2+(5459639059/10000000000 : ℝ)*X 2 0+(5451209921/10000000000 : ℝ)*X 2 1+(-1825874703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-2010201671/10000000000 : ℝ)*X 0 0+(1103130101/2500000000 : ℝ)*X 0 1+(-3156006201/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((1202602801/2500000000 : ℝ)*X 1 0+(-338580637/2000000000 : ℝ)*X 1 1+(-3082440857/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((2446175723/5000000000 : ℝ)*X 2 0+(589698097/1000000000 : ℝ)*X 2 1+(19755421/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((161895869/312500000 : ℝ)*X 0 0+(759791581/1250000000 : ℝ)*X 0 1+(-1279990817/10000000000 : ℝ)*X 0 2+(161895869/312500000 : ℝ)*X 1 0+(759791581/1250000000 : ℝ)*X 1 1+(-1279990817/10000000000 : ℝ)*X 1 2+(161895869/312500000 : ℝ)*X 2 0+(759791581/1250000000 : ℝ)*X 2 1+(-1279990817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-811657181/5000000000 : ℝ)*X 0 0+(2371216483/5000000000 : ℝ)*X 0 1+(-1568110487/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((179567643/400000000 : ℝ)*X 1 0+(-1043830239/5000000000 : ℝ)*X 1 1+(-3094787913/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((5808688263/10000000000 : ℝ)*X 2 0+(4975536547/10000000000 : ℝ)*X 2 1+(497310259/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((3118689517/5000000000 : ℝ)*X 0 0+(5010003513/10000000000 : ℝ)*X 0 1+(-1282298521/10000000000 : ℝ)*X 0 2+(3118689517/5000000000 : ℝ)*X 1 0+(5010003513/10000000000 : ℝ)*X 1 1+(-1282298521/10000000000 : ℝ)*X 1 2+(3118689517/5000000000 : ℝ)*X 2 0+(5010003513/10000000000 : ℝ)*X 2 1+(-1282298521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-1407711383/10000000000 : ℝ)*X 0 0+(32699483/62500000 : ℝ)*X 0 1+(-5951153847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((2893396943/5000000000 : ℝ)*X 1 0+(-1969307933/10000000000 : ℝ)*X 1 1+(-626657189/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((14629713/31250000 : ℝ)*X 2 0+(5465019257/10000000000 : ℝ)*X 2 1+(2813554391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((3162932451/5000000000 : ℝ)*X 0 0+(4778212913/10000000000 : ℝ)*X 0 1+(-92962567/625000000 : ℝ)*X 0 2+(3162932451/5000000000 : ℝ)*X 1 0+(4778212913/10000000000 : ℝ)*X 1 1+(-92962567/625000000 : ℝ)*X 1 2+(3162932451/5000000000 : ℝ)*X 2 0+(4778212913/10000000000 : ℝ)*X 2 1+(-92962567/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((34121/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34121/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2865631171041656910256773/414531050000000000000000000000 : ℝ) := by norm_num
    linear_combination (373187826469/1000000000000 : ℝ)*(base39) + (116904518573/500000000000 : ℝ)*(base49) + (141956668151/1000000000000 : ℝ)*(base60) + (430794002461/62500000000 : ℝ)*(major_s5_0) + (430794002461/62500000000 : ℝ)*(major_s5_1) + (430794002461/62500000000 : ℝ)*(major_s5_2) + (1468467/500000000000 : ℝ)*(sp_s5_0) + (2230959/50000000000 : ℝ)*(sp_s5_1) + (9125777597931/1000000000000 : ℝ)*(sp_s5_7) + (4562838721807/500000000000 : ℝ)*(sp_s5_8) + (9125704071449/1000000000000 : ℝ)*(sp_s5_9) + (2329812619783/500000000000 : ℝ)*(sp_s5_13) + (7309009/125000000000 : ℝ)*(sp_s5_15) + (76463417/1000000000000 : ℝ)*(sp_s5_23) + (2329812619783/500000000000 : ℝ)*(f.failure) + (1825156106973/200000000000 : ℝ)*(f.sum) + (429687099273221201/1243593150000000000000000000000 : ℝ)*base63 + (2246010000931/63487500000000000000000000 : ℝ)*base65 + (5909367509359/45909375000000000000000000 : ℝ)*base66 + (11410478156849/126975000000000000000000000 : ℝ)*base69 + (31551955059757823/1853136637500000000000000000000 : ℝ)*base71 + (29389251443381/145945000000000000000000000 : ℝ)*base73 + (13042491584753/73455000000000000000000000 : ℝ)*base74 + (285767469124771/1459450000000000000000000000 : ℝ)*base76 + (4230126688536433391/21440779950000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (4877/12500000000000000 : ℝ)*base86 + (4877/12500000000000000 : ℝ)*base88 + (4877/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34301/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34301/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (182219792938329021136741103413/24199493636900000000000000000000000 : ℝ) := by norm_num
    linear_combination (22126844269/62500000000 : ℝ)*(base39) + (54453844891/200000000000 : ℝ)*(base49) + (8941/62500000000 : ℝ)*(base60) + (6980599283221/1000000000000 : ℝ)*(major_s5_0) + (6980599283221/1000000000000 : ℝ)*(major_s5_1) + (6980599283221/1000000000000 : ℝ)*(major_s5_2) + (363009/31250000000 : ℝ)*(sp_s5_6) + (14758401/500000000000 : ℝ)*(sp_s5_7) + (16628803/250000000000 : ℝ)*(sp_s5_8) + (9242122109271/1000000000000 : ℝ)*(sp_s5_14) + (9242085110861/1000000000000 : ℝ)*(sp_s5_15) + (9242151626073/1000000000000 : ℝ)*(sp_s5_16) + (117972039153/25000000000 : ℝ)*(sp_s5_20) + (151247989/1000000000000 : ℝ)*(sp_s5_27) + (4719044430397/1000000000000 : ℝ)*(f.failure) + (9242151626073/1000000000000 : ℝ)*(f.sum) + (1240740365048732237/9948745200000000000000000000000 : ℝ)*base62 + (1026664201248497/2031600000000000000000000000 : ℝ)*base65 + (217955636183869/734550000000000000000000000 : ℝ)*base66 + (279822585435901/2031600000000000000000000000 : ℝ)*base68 + (32821853629935687781/59300372400000000000000000000000 : ℝ)*base71 + (75427437621877/583780000000000000000000000 : ℝ)*base73 + (15281628523681/73455000000000000000000000 : ℝ)*base75 + (132785829502127/729725000000000000000000000 : ℝ)*base77 + (5665304572465898587/42881559900000000000000000000000 : ℝ)*base78 + (13543/25000000000000000 : ℝ)*base86 + (13543/25000000000000000 : ℝ)*base88 + (13543/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5293/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5293/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15806226465449246558077897/1658124200000000000000000000000 : ℝ) := by norm_num
    linear_combination (164651/250000000000 : ℝ)*(base11) + (21790054379/25000000000 : ℝ)*(base39) + (2391231/1000000000000 : ℝ)*(base40) + (84479089109/500000000000 : ℝ)*(base49) + (5624902462999/1000000000000 : ℝ)*(major_s5_0) + (5624902462999/1000000000000 : ℝ)*(major_s5_1) + (5624902462999/1000000000000 : ℝ)*(major_s5_2) + (1705223/50000000000 : ℝ)*(sp_s5_0) + (77807787/1000000000000 : ℝ)*(sp_s5_9) + (7850253/100000000000 : ℝ)*(sp_s5_20) + (74472045459/10000000000 : ℝ)*(sp_s5_21) + (1861809827241/250000000000 : ℝ)*(sp_s5_22) + (7447161501177/1000000000000 : ℝ)*(sp_s5_23) + (1901241968483/500000000000 : ℝ)*(sp_s5_27) + (760512487899/200000000000 : ℝ)*(f.failure) + (1861809827241/250000000000 : ℝ)*(f.sum) + (2713104093163782863/9948745200000000000000000000000 : ℝ)*base62 + (1470260194283677/2031600000000000000000000000 : ℝ)*base64 + (83891612660819/734550000000000000000000000 : ℝ)*base67 + (1671204030185959/2031600000000000000000000000 : ℝ)*base68 + (8896830336519626719/59300372400000000000000000000000 : ℝ)*base71 + (177463689902591/583780000000000000000000000 : ℝ)*base73 + (23429130379007/29382000000000000000000000 : ℝ)*base74 + (584688944535309/1459450000000000000000000000 : ℝ)*base76 + (28543603977420432343/42881559900000000000000000000000 : ℝ)*base78 + (2081/5000000000000000 : ℝ)*base86 + (2081/5000000000000000 : ℝ)*base88 + (2081/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev4 : (0 : ℝ) ≤ ((29189/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29189/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14691/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14691/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5079/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5079/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((34121/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34121/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34301/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34301/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5293/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5293/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301062_s5 p hpa hpb X hX hprev4

#print axioms solution
