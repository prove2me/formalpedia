-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1440_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:56:42.659909+00:00
-- url     : https://prove2.me/submissions/aaa2d5bf-9f99-43ff-9d76-48a4cb598eba

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1440_s3_0 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-245156377/1250000000 : ℝ)*x 0 + (5416183857/10000000000 : ℝ)*x 1 + (5239266857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (245156377/1250000000 : ℝ)^275 ≤ (1196591985557/10000000000000 : ℝ)^211 := by
    have hnat : (245156377 : ℕ)^275*10000000000000^211 ≤ 1196591985557^211*1250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245156377 1250000000 1196591985557 10000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416183857/10000000000 : ℝ)^275 ≤ (22484743658259/50000000000000 : ℝ)^211 := by
    have hnat : (5416183857 : ℕ)^275*50000000000000^211 ≤ 22484743658259^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416183857 10000000000 22484743658259 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239266857/10000000000 : ℝ)^275 ≤ (1722583712369/4000000000000 : ℝ)^211 := by
    have hnat : (5239266857 : ℕ)^275*4000000000000^211 ≤ 1722583712369^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239266857 10000000000 1722583712369 4000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-245156377/1250000000 : ℝ), (5416183857/10000000000 : ℝ), (5239266857/10000000000 : ℝ)] ![(1196591985557/10000000000000 : ℝ), (22484743658259/50000000000000 : ℝ), (1722583712369/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-245156377/1250000000 : ℝ)|^275 ≤ (1196591985557/10000000000000 : ℝ)^211
        have hw : |(-245156377/1250000000 : ℝ)|=(245156377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416183857/10000000000 : ℝ)|^275 ≤ (22484743658259/50000000000000 : ℝ)^211
        have hw : |(5416183857/10000000000 : ℝ)|=(5416183857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239266857/10000000000 : ℝ)|^275 ≤ (1722583712369/4000000000000 : ℝ)^211
        have hw : |(5239266857/10000000000 : ℝ)|=(5239266857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s3_1 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (133732479/250000000 : ℝ)*x 0 + (-1025739133/5000000000 : ℝ)*x 1 + (5239266261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133732479/250000000 : ℝ)^275 ≤ (44247075129153/100000000000000 : ℝ)^211 := by
    have hnat : (133732479 : ℕ)^275*100000000000000^211 ≤ 44247075129153^211*250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133732479 250000000 44247075129153 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025739133/5000000000 : ℝ)^275 ≤ (12688338431663/100000000000000 : ℝ)^211 := by
    have hnat : (1025739133 : ℕ)^275*100000000000000^211 ≤ 12688338431663^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025739133 5000000000 12688338431663 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239266261/10000000000 : ℝ)^275 ≤ (43064586424439/100000000000000 : ℝ)^211 := by
    have hnat : (5239266261 : ℕ)^275*100000000000000^211 ≤ 43064586424439^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239266261 10000000000 43064586424439 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133732479/250000000 : ℝ), (-1025739133/5000000000 : ℝ), (5239266261/10000000000 : ℝ)] ![(44247075129153/100000000000000 : ℝ), (12688338431663/100000000000000 : ℝ), (43064586424439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133732479/250000000 : ℝ)|^275 ≤ (44247075129153/100000000000000 : ℝ)^211
        have hw : |(133732479/250000000 : ℝ)|=(133732479/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025739133/5000000000 : ℝ)|^275 ≤ (12688338431663/100000000000000 : ℝ)^211
        have hw : |(-1025739133/5000000000 : ℝ)|=(1025739133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239266261/10000000000 : ℝ)|^275 ≤ (43064586424439/100000000000000 : ℝ)^211
        have hw : |(5239266261/10000000000 : ℝ)|=(5239266261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s3_2 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1337324773/2500000000 : ℝ)*x 0 + (5239266349/10000000000 : ℝ)*x 1 + (-12821739/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337324773/2500000000 : ℝ)^275 ≤ (553088429951/1250000000000 : ℝ)^211 := by
    have hnat : (1337324773 : ℕ)^275*1250000000000^211 ≤ 553088429951^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337324773 2500000000 553088429951 1250000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239266349/10000000000 : ℝ)^275 ≤ (43064587367159/100000000000000 : ℝ)^211 := by
    have hnat : (5239266349 : ℕ)^275*100000000000000^211 ≤ 43064587367159^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239266349 10000000000 43064587367159 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12821739/62500000 : ℝ)^275 ≤ (12688338222077/100000000000000 : ℝ)^211 := by
    have hnat : (12821739 : ℕ)^275*100000000000000^211 ≤ 12688338222077^211*62500000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12821739 62500000 12688338222077 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337324773/2500000000 : ℝ), (5239266349/10000000000 : ℝ), (-12821739/62500000 : ℝ)] ![(553088429951/1250000000000 : ℝ), (43064587367159/100000000000000 : ℝ), (12688338222077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337324773/2500000000 : ℝ)|^275 ≤ (553088429951/1250000000000 : ℝ)^211
        have hw : |(1337324773/2500000000 : ℝ)|=(1337324773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239266349/10000000000 : ℝ)|^275 ≤ (43064587367159/100000000000000 : ℝ)^211
        have hw : |(5239266349/10000000000 : ℝ)|=(5239266349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12821739/62500000 : ℝ)|^275 ≤ (12688338222077/100000000000000 : ℝ)^211
        have hw : |(-12821739/62500000 : ℝ)|=(12821739/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s3_3 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4301023929/10000000000 : ℝ)*x 0 + (1028182067/2500000000 : ℝ)*x 1 + (281062613/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301023929/10000000000 : ℝ)^275 ≤ (16649369141431/50000000000000 : ℝ)^211 := by
    have hnat : (4301023929 : ℕ)^275*50000000000000^211 ≤ 16649369141431^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301023929 10000000000 16649369141431 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028182067/2500000000 : ℝ)^275 ≤ (7852878757691/25000000000000 : ℝ)^211 := by
    have hnat : (1028182067 : ℕ)^275*25000000000000^211 ≤ 7852878757691^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028182067 2500000000 7852878757691 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281062613/625000000 : ℝ)^275 ≤ (17644873334657/50000000000000 : ℝ)^211 := by
    have hnat : (281062613 : ℕ)^275*50000000000000^211 ≤ 17644873334657^211*625000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281062613 625000000 17644873334657 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301023929/10000000000 : ℝ), (1028182067/2500000000 : ℝ), (281062613/625000000 : ℝ)] ![(16649369141431/50000000000000 : ℝ), (7852878757691/25000000000000 : ℝ), (17644873334657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301023929/10000000000 : ℝ)|^275 ≤ (16649369141431/50000000000000 : ℝ)^211
        have hw : |(4301023929/10000000000 : ℝ)|=(4301023929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028182067/2500000000 : ℝ)|^275 ≤ (7852878757691/25000000000000 : ℝ)^211
        have hw : |(1028182067/2500000000 : ℝ)|=(1028182067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281062613/625000000 : ℝ)|^275 ≤ (17644873334657/50000000000000 : ℝ)^211
        have hw : |(281062613/625000000 : ℝ)|=(281062613/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s3_4 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-980632807/5000000000 : ℝ)*x 0 + (523997039/1000000000 : ℝ)*x 1 + (270773831/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980632807/5000000000 : ℝ)^275 ≤ (11966035935463/100000000000000 : ℝ)^211 := by
    have hnat : (980632807 : ℕ)^275*100000000000000^211 ≤ 11966035935463^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980632807 5000000000 11966035935463 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523997039/1000000000 : ℝ)^275 ≤ (43072129720133/100000000000000 : ℝ)^211 := by
    have hnat : (523997039 : ℕ)^275*100000000000000^211 ≤ 43072129720133^211*1000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523997039 1000000000 43072129720133 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270773831/500000000 : ℝ)^275 ≤ (702528661351/1562500000000 : ℝ)^211 := by
    have hnat : (270773831 : ℕ)^275*1562500000000^211 ≤ 702528661351^211*500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270773831 500000000 702528661351 1562500000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-980632807/5000000000 : ℝ), (523997039/1000000000 : ℝ), (270773831/500000000 : ℝ)] ![(11966035935463/100000000000000 : ℝ), (43072129720133/100000000000000 : ℝ), (702528661351/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-980632807/5000000000 : ℝ)|^275 ≤ (11966035935463/100000000000000 : ℝ)^211
        have hw : |(-980632807/5000000000 : ℝ)|=(980632807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523997039/1000000000 : ℝ)|^275 ≤ (43072129720133/100000000000000 : ℝ)^211
        have hw : |(523997039/1000000000 : ℝ)|=(523997039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270773831/500000000 : ℝ)|^275 ≤ (702528661351/1562500000000 : ℝ)^211
        have hw : |(270773831/500000000 : ℝ)|=(270773831/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s3_5 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2651628401/5000000000 : ℝ)*x 0 + (-1875268463/10000000000 : ℝ)*x 1 + (5415476561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651628401/5000000000 : ℝ)^275 ≤ (2187568291839/5000000000000 : ℝ)^211 := by
    have hnat : (2651628401 : ℕ)^275*5000000000000^211 ≤ 2187568291839^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651628401 5000000000 2187568291839 5000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1875268463/10000000000 : ℝ)^275 ≤ (11286800459407/100000000000000 : ℝ)^211 := by
    have hnat : (1875268463 : ℕ)^275*100000000000000^211 ≤ 11286800459407^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875268463 10000000000 11286800459407 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415476561/10000000000 : ℝ)^275 ≤ (1124045842201/2500000000000 : ℝ)^211 := by
    have hnat : (5415476561 : ℕ)^275*2500000000000^211 ≤ 1124045842201^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415476561 10000000000 1124045842201 2500000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651628401/5000000000 : ℝ), (-1875268463/10000000000 : ℝ), (5415476561/10000000000 : ℝ)] ![(2187568291839/5000000000000 : ℝ), (11286800459407/100000000000000 : ℝ), (1124045842201/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651628401/5000000000 : ℝ)|^275 ≤ (2187568291839/5000000000000 : ℝ)^211
        have hw : |(2651628401/5000000000 : ℝ)|=(2651628401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1875268463/10000000000 : ℝ)|^275 ≤ (11286800459407/100000000000000 : ℝ)^211
        have hw : |(-1875268463/10000000000 : ℝ)|=(1875268463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415476561/10000000000 : ℝ)|^275 ≤ (1124045842201/2500000000000 : ℝ)^211
        have hw : |(5415476561/10000000000 : ℝ)|=(5415476561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s3_6 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2651627749/5000000000 : ℝ)*x 0 + (1353869407/2500000000 : ℝ)*x 1 + (-937634389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651627749/5000000000 : ℝ)^275 ≤ (10937837953963/25000000000000 : ℝ)^211 := by
    have hnat : (2651627749 : ℕ)^275*25000000000000^211 ≤ 10937837953963^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651627749 5000000000 10937837953963 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353869407/2500000000 : ℝ)^275 ≤ (22480922616893/50000000000000 : ℝ)^211 := by
    have hnat : (1353869407 : ℕ)^275*50000000000000^211 ≤ 22480922616893^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353869407 2500000000 22480922616893 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937634389/5000000000 : ℝ)^275 ≤ (11286802930381/100000000000000 : ℝ)^211 := by
    have hnat : (937634389 : ℕ)^275*100000000000000^211 ≤ 11286802930381^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937634389 5000000000 11286802930381 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651627749/5000000000 : ℝ), (1353869407/2500000000 : ℝ), (-937634389/5000000000 : ℝ)] ![(10937837953963/25000000000000 : ℝ), (22480922616893/50000000000000 : ℝ), (11286802930381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651627749/5000000000 : ℝ)|^275 ≤ (10937837953963/25000000000000 : ℝ)^211
        have hw : |(2651627749/5000000000 : ℝ)|=(2651627749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353869407/2500000000 : ℝ)|^275 ≤ (22480922616893/50000000000000 : ℝ)^211
        have hw : |(1353869407/2500000000 : ℝ)|=(1353869407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-937634389/5000000000 : ℝ)|^275 ≤ (11286802930381/100000000000000 : ℝ)^211
        have hw : |(-937634389/5000000000 : ℝ)|=(937634389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s3_7 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2150527863/5000000000 : ℝ)*x 0 + (4495474463/10000000000 : ℝ)*x 1 + (4114265161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150527863/5000000000 : ℝ)^275 ≤ (33299059126027/100000000000000 : ℝ)^211 := by
    have hnat : (2150527863 : ℕ)^275*100000000000000^211 ≤ 33299059126027^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150527863 5000000000 33299059126027 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495474463/10000000000 : ℝ)^275 ≤ (35274126328969/100000000000000 : ℝ)^211 := by
    have hnat : (4495474463 : ℕ)^275*100000000000000^211 ≤ 35274126328969^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495474463 10000000000 35274126328969 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4114265161/10000000000 : ℝ)^275 ≤ (31426814534667/100000000000000 : ℝ)^211 := by
    have hnat : (4114265161 : ℕ)^275*100000000000000^211 ≤ 31426814534667^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114265161 10000000000 31426814534667 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150527863/5000000000 : ℝ), (4495474463/10000000000 : ℝ), (4114265161/10000000000 : ℝ)] ![(33299059126027/100000000000000 : ℝ), (35274126328969/100000000000000 : ℝ), (31426814534667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150527863/5000000000 : ℝ)|^275 ≤ (33299059126027/100000000000000 : ℝ)^211
        have hw : |(2150527863/5000000000 : ℝ)|=(2150527863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495474463/10000000000 : ℝ)|^275 ≤ (35274126328969/100000000000000 : ℝ)^211
        have hw : |(4495474463/10000000000 : ℝ)|=(4495474463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4114265161/10000000000 : ℝ)|^275 ≤ (31426814534667/100000000000000 : ℝ)^211
        have hw : |(4114265161/10000000000 : ℝ)|=(4114265161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1440_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (417/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (5597/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14941/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7883/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (417/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7883/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (417/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7883/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (417/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7883/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (417/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7883/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (417/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7883/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (417/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (417/4000 : ℝ) ^ (4399/1024 : ℝ) ≤ (6049987760826019/100000000000000000000 : ℝ) := by
    have hpowers : (417/4000 : ℝ)^4399 ≤ (6049987760826019/100000000000000000000 : ℝ)^1024 := by
      have hnat : (417 : ℕ)^4399*100000000000000000000^1024 ≤ 6049987760826019^1024*4000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        417 4000 6049987760826019 100000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (417/4000 : ℝ)) (X := (6049987760826019/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7883/50000 : ℝ) ^ (4399/1024 : ℝ) ≤ (35767875147025077/100000000000000000000 : ℝ) := by
    have hpowers : (7883/50000 : ℝ)^4399 ≤ (35767875147025077/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7883 : ℕ)^4399*100000000000000000000^1024 ≤ 35767875147025077^1024*50000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7883 50000 35767875147025077 100000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7883/50000 : ℝ)) (X := (35767875147025077/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006049987760826019/50000000000000000000 : ℝ) ≤ (2000056330074357/2000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (50006049987760826019/50000000000000000000 : ℝ)^1024 ≤ (2000056330074357/2000000000000000 : ℝ)^4399 := by
      have hnat : (50006049987760826019 : ℕ)^1024*2000000000000000^4399 ≤ 2000056330074357^4399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006049987760826019 50000000000000000000 2000056330074357 2000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056330074357/2000000000000000 : ℝ)) (X := (50006049987760826019/50000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505227232863481387/12500000000000000000 : ℝ) ≤ (500048664041821/500000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (12505227232863481387/12500000000000000000 : ℝ)^1024 ≤ (500048664041821/500000000000000 : ℝ)^4399 := by
      have hnat : (12505227232863481387 : ℕ)^1024*500000000000000^4399 ≤ 500048664041821^4399*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505227232863481387 12500000000000000000 500048664041821 500000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500048664041821/500000000000000 : ℝ)) (X := (12505227232863481387/12500000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035767875147025077/50000000000000000000 : ℝ) ≤ (2000332982260211/2000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (50035767875147025077/50000000000000000000 : ℝ)^1024 ≤ (2000332982260211/2000000000000000 : ℝ)^4399 := by
      have hnat : (50035767875147025077 : ℕ)^1024*2000000000000000^4399 ≤ 2000332982260211^4399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035767875147025077 50000000000000000000 2000332982260211 2000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000332982260211/2000000000000000 : ℝ)) (X := (50035767875147025077/50000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6049987760826019/100000000000000000000 : ℝ) ≤ ((10679416759889612787/10682000000000000000 : ℝ)+2*(138326092927/106820000000000 : ℝ)*(417/4000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (10679416759889612787/10682000000000000000 : ℝ)+2*(138326092927/106820000000000 : ℝ)*(417/4000 : ℝ)=(2000056330074357/2000000000000000 : ℝ) by norm_num, show 1+2*(6049987760826019/100000000000000000000 : ℝ)=(50006049987760826019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35767875147025077/100000000000000000000 : ℝ)+(6049987760826019/100000000000000000000 : ℝ) ≤ ((10679416759889612787/10682000000000000000 : ℝ)+(138326092927/106820000000000 : ℝ)*((7883/50000 : ℝ)+(417/4000 : ℝ)))^(4399/1024 : ℝ) := by
    rw [show (10679416759889612787/10682000000000000000 : ℝ)+(138326092927/106820000000000 : ℝ)*((7883/50000 : ℝ)+(417/4000 : ℝ))=(500048664041821/500000000000000 : ℝ) by norm_num, show 1+(35767875147025077/100000000000000000000 : ℝ)+(6049987760826019/100000000000000000000 : ℝ)=(12505227232863481387/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35767875147025077/100000000000000000000 : ℝ) ≤ ((10679416759889612787/10682000000000000000 : ℝ)+2*(138326092927/106820000000000 : ℝ)*(7883/50000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (10679416759889612787/10682000000000000000 : ℝ)+2*(138326092927/106820000000000 : ℝ)*(7883/50000 : ℝ)=(2000332982260211/2000000000000000 : ℝ) by norm_num, show 1+2*(35767875147025077/100000000000000000000 : ℝ)=(50035767875147025077/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10679416759889612787/10682000000000000000 : ℝ)*(X 1 0+X 2 0)+(138326092927/106820000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (417/4000 : ℝ)) (hi := (7883/50000 : ℝ)) (c := (10679416759889612787/10682000000000000000 : ℝ)) (alpha := (138326092927/106820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10679416759889612787/10682000000000000000 : ℝ)*(X 0 1+X 2 1)+(138326092927/106820000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (417/4000 : ℝ)) (hi := (7883/50000 : ℝ)) (c := (10679416759889612787/10682000000000000000 : ℝ)) (alpha := (138326092927/106820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10679416759889612787/10682000000000000000 : ℝ)*(X 0 2+X 1 2)+(138326092927/106820000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (417/4000 : ℝ)) (hi := (7883/50000 : ℝ)) (c := (10679416759889612787/10682000000000000000 : ℝ)) (alpha := (138326092927/106820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-245156377/1250000000 : ℝ)*X 0 0+(5416183857/10000000000 : ℝ)*X 0 1+(5239266857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133732479/250000000 : ℝ)*X 1 0+(-1025739133/5000000000 : ℝ)*X 1 1+(5239266261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337324773/2500000000 : ℝ)*X 2 0+(5239266349/10000000000 : ℝ)*X 2 1+(-12821739/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4301023929/10000000000 : ℝ)*X 0 0+(1028182067/2500000000 : ℝ)*X 0 1+(281062613/625000000 : ℝ)*X 0 2+(4301023929/10000000000 : ℝ)*X 1 0+(1028182067/2500000000 : ℝ)*X 1 1+(281062613/625000000 : ℝ)*X 1 2+(4301023929/10000000000 : ℝ)*X 2 0+(1028182067/2500000000 : ℝ)*X 2 1+(281062613/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-980632807/5000000000 : ℝ)*X 0 0+(523997039/1000000000 : ℝ)*X 0 1+(270773831/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651628401/5000000000 : ℝ)*X 1 0+(-1875268463/10000000000 : ℝ)*X 1 1+(5415476561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651627749/5000000000 : ℝ)*X 2 0+(1353869407/2500000000 : ℝ)*X 2 1+(-937634389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2150527863/5000000000 : ℝ)*X 0 0+(4495474463/10000000000 : ℝ)*X 0 1+(4114265161/10000000000 : ℝ)*X 0 2+(2150527863/5000000000 : ℝ)*X 1 0+(4495474463/10000000000 : ℝ)*X 1 1+(4114265161/10000000000 : ℝ)*X 1 2+(2150527863/5000000000 : ℝ)*X 2 0+(4495474463/10000000000 : ℝ)*X 2 1+(4114265161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1100499891323109312288662133/133525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (326421307/25000000000000 : ℝ)*(base19) + (1182163159/100000000000000 : ℝ)*(base23) + (1727463/6250000000000 : ℝ)*(lower2) + (98077963/100000000000000 : ℝ)*(upper3) + (39050607/50000000000000 : ℝ)*(upper5) + (1031839015310947/25000000000000 : ℝ)*(major0) + (1031839015310947/25000000000000 : ℝ)*(major1) + (1031839015310947/25000000000000 : ℝ)*(major2) + (5652379183944683/100000000000000 : ℝ)*(sp0) + (353274279391913/6250000000000 : ℝ)*(sp1) + (2826194296896339/50000000000000 : ℝ)*(sp2) + (1301158679167341/50000000000000 : ℝ)*(sp3) + (10592011153/100000000000000 : ℝ)*(sp4) + (4713466999/100000000000000 : ℝ)*(sp7) + (2602322071801681/100000000000000 : ℝ)*(f.failure) + (5652389775955837/100000000000000 : ℝ)*(f.sum) + (2212382296307/2670500000000000000000000000 : ℝ)*base65 + (2811252466615479289/267050000000000000000000000000000 : ℝ)*base67 + (1262319265402879289/267050000000000000000000000000000 : ℝ)*base69 + (1201688221118579289/267050000000000000000000000000000 : ℝ)*base71 + (23200085491991/5341000000000000000000000000 : ℝ)*base73 + (345413198420970711/267050000000000000000000000000000 : ℝ)*base76 + (957455214531779289/267050000000000000000000000000000 : ℝ)*base77 + (2586535881722570711/267050000000000000000000000000000 : ℝ)*base80 + (4344386852801/5341000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (14333597/2000000000000000000000 : ℝ)*base90 + (14333597/2000000000000000000000 : ℝ)*base92 + (14333597/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35450727231187703992029/5341000000000000000000000000 : ℝ) := by norm_num
    linear_combination (257756231/100000000000000 : ℝ)*(base8) + (1229700821/100000000000000 : ℝ)*(base21) + (168324263/100000000000000 : ℝ)*(upper2) + (1494477/100000000000000 : ℝ)*(lower4) + (2080260395799529/50000000000000 : ℝ)*(major0) + (2080260395799529/50000000000000 : ℝ)*(major1) + (2080260395799529/50000000000000 : ℝ)*(major2) + (335460421/25000000000000 : ℝ)*(sp0) + (229865203/3125000000000 : ℝ)*(sp1) + (6403448923/100000000000000 : ℝ)*(sp2) + (2848903567304037/50000000000000 : ℝ)*(sp4) + (1424450344629873/25000000000000 : ℝ)*(sp5) + (1139560220211249/20000000000000 : ℝ)*(sp6) + (2623232627743119/100000000000000 : ℝ)*(sp7) + (2623232627743119/100000000000000 : ℝ)*(f.failure) + (5697808734205989/100000000000000 : ℝ)*(f.sum) + (398826704953/83453125000000000000000000 : ℝ)*base65 + (2218020053380777323/534100000000000000000000000000000 : ℝ)*base67 + (706754318415422677/534100000000000000000000000000000 : ℝ)*base70 + (1118477359999477323/534100000000000000000000000000000 : ℝ)*base71 + (13328936700301/5341000000000000000000000000 : ℝ)*base73 + (2234943350155422677/534100000000000000000000000000000 : ℝ)*base76 + (18889461423886722677/534100000000000000000000000000000 : ℝ)*base78 + (1023796520460877323/534100000000000000000000000000000 : ℝ)*base79 + (6671755864877/5341000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5944003/2000000000000000000000 : ℝ)*base90 + (5944003/2000000000000000000000 : ℝ)*base92 + (5944003/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1440_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (417/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5597/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14941/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1440_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1440_s4_0 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-490524227/2500000000 : ℝ)*x 0 + (67611519/125000000 : ℝ)*x 1 + (2622986001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490524227/2500000000 : ℝ)^275 ≤ (5986323311929/50000000000000 : ℝ)^211 := by
    have hnat : (490524227 : ℕ)^275*50000000000000^211 ≤ 5986323311929^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490524227 2500000000 5986323311929 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67611519/125000000 : ℝ)^275 ≤ (44890916218419/100000000000000 : ℝ)^211 := by
    have hnat : (67611519 : ℕ)^275*100000000000000^211 ≤ 44890916218419^211*125000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67611519 125000000 44890916218419 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622986001/5000000000 : ℝ)^275 ≤ (8627287427801/20000000000000 : ℝ)^211 := by
    have hnat : (2622986001 : ℕ)^275*20000000000000^211 ≤ 8627287427801^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622986001 5000000000 8627287427801 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-490524227/2500000000 : ℝ), (67611519/125000000 : ℝ), (2622986001/5000000000 : ℝ)] ![(5986323311929/50000000000000 : ℝ), (44890916218419/100000000000000 : ℝ), (8627287427801/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-490524227/2500000000 : ℝ)|^275 ≤ (5986323311929/50000000000000 : ℝ)^211
        have hw : |(-490524227/2500000000 : ℝ)|=(490524227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67611519/125000000 : ℝ)|^275 ≤ (44890916218419/100000000000000 : ℝ)^211
        have hw : |(67611519/125000000 : ℝ)|=(67611519/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622986001/5000000000 : ℝ)|^275 ≤ (8627287427801/20000000000000 : ℝ)^211
        have hw : |(2622986001/5000000000 : ℝ)|=(2622986001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s4_1 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5347421973/10000000000 : ℝ)*x 0 + (-204507193/1000000000 : ℝ)*x 1 + (1311493049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347421973/10000000000 : ℝ)^275 ≤ (22113419618833/50000000000000 : ℝ)^211 := by
    have hnat : (5347421973 : ℕ)^275*50000000000000^211 ≤ 22113419618833^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347421973 10000000000 22113419618833 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204507193/1000000000 : ℝ)^275 ≤ (2527344306631/20000000000000 : ℝ)^211 := by
    have hnat : (204507193 : ℕ)^275*20000000000000^211 ≤ 2527344306631^211*1000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204507193 1000000000 2527344306631 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311493049/2500000000 : ℝ)^275 ≤ (43136439218081/100000000000000 : ℝ)^211 := by
    have hnat : (1311493049 : ℕ)^275*100000000000000^211 ≤ 43136439218081^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311493049 2500000000 43136439218081 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347421973/10000000000 : ℝ), (-204507193/1000000000 : ℝ), (1311493049/2500000000 : ℝ)] ![(22113419618833/50000000000000 : ℝ), (2527344306631/20000000000000 : ℝ), (43136439218081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347421973/10000000000 : ℝ)|^275 ≤ (22113419618833/50000000000000 : ℝ)^211
        have hw : |(5347421973/10000000000 : ℝ)|=(5347421973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-204507193/1000000000 : ℝ)|^275 ≤ (2527344306631/20000000000000 : ℝ)^211
        have hw : |(-204507193/1000000000 : ℝ)|=(204507193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311493049/2500000000 : ℝ)|^275 ≤ (43136439218081/100000000000000 : ℝ)^211
        have hw : |(1311493049/2500000000 : ℝ)|=(1311493049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s4_2 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5347422057/10000000000 : ℝ)*x 0 + (2622986101/5000000000 : ℝ)*x 1 + (-2045071809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347422057/10000000000 : ℝ)^275 ≤ (44226840143129/100000000000000 : ℝ)^211 := by
    have hnat : (5347422057 : ℕ)^275*100000000000000^211 ≤ 44226840143129^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347422057 10000000000 44226840143129 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622986101/5000000000 : ℝ)^275 ≤ (21568219641191/50000000000000 : ℝ)^211 := by
    have hnat : (2622986101 : ℕ)^275*50000000000000^211 ≤ 21568219641191^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622986101 5000000000 21568219641191 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2045071809/10000000000 : ℝ)^275 ≤ (12636720558701/100000000000000 : ℝ)^211 := by
    have hnat : (2045071809 : ℕ)^275*100000000000000^211 ≤ 12636720558701^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045071809 10000000000 12636720558701 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347422057/10000000000 : ℝ), (2622986101/5000000000 : ℝ), (-2045071809/10000000000 : ℝ)] ![(44226840143129/100000000000000 : ℝ), (21568219641191/50000000000000 : ℝ), (12636720558701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347422057/10000000000 : ℝ)|^275 ≤ (44226840143129/100000000000000 : ℝ)^211
        have hw : |(5347422057/10000000000 : ℝ)|=(5347422057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622986101/5000000000 : ℝ)|^275 ≤ (21568219641191/50000000000000 : ℝ)^211
        have hw : |(2622986101/5000000000 : ℝ)|=(2622986101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2045071809/10000000000 : ℝ)|^275 ≤ (12636720558701/100000000000000 : ℝ)^211
        have hw : |(-2045071809/10000000000 : ℝ)|=(2045071809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s4_3 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1075385941/2500000000 : ℝ)*x 0 + (4127834921/10000000000 : ℝ)*x 1 + (2240885037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075385941/2500000000 : ℝ)^275 ≤ (16651991847609/50000000000000 : ℝ)^211 := by
    have hnat : (1075385941 : ℕ)^275*50000000000000^211 ≤ 16651991847609^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075385941 2500000000 16651991847609 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127834921/10000000000 : ℝ)^275 ≤ (15780987161833/50000000000000 : ℝ)^211 := by
    have hnat : (4127834921 : ℕ)^275*50000000000000^211 ≤ 15780987161833^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127834921 10000000000 15780987161833 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240885037/5000000000 : ℝ)^275 ≤ (35134041962257/100000000000000 : ℝ)^211 := by
    have hnat : (2240885037 : ℕ)^275*100000000000000^211 ≤ 35134041962257^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240885037 5000000000 35134041962257 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075385941/2500000000 : ℝ), (4127834921/10000000000 : ℝ), (2240885037/5000000000 : ℝ)] ![(16651991847609/50000000000000 : ℝ), (15780987161833/50000000000000 : ℝ), (35134041962257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075385941/2500000000 : ℝ)|^275 ≤ (16651991847609/50000000000000 : ℝ)^211
        have hw : |(1075385941/2500000000 : ℝ)|=(1075385941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127834921/10000000000 : ℝ)|^275 ≤ (15780987161833/50000000000000 : ℝ)^211
        have hw : |(4127834921/10000000000 : ℝ)|=(4127834921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240885037/5000000000 : ℝ)|^275 ≤ (35134041962257/100000000000000 : ℝ)^211
        have hw : |(2240885037/5000000000 : ℝ)|=(2240885037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s4_4 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-981054357/5000000000 : ℝ)*x 0 + (2623284629/5000000000 : ℝ)*x 1 + (135208027/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981054357/5000000000 : ℝ)^275 ≤ (11972740514677/100000000000000 : ℝ)^211 := by
    have hnat : (981054357 : ℕ)^275*100000000000000^211 ≤ 11972740514677^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981054357 5000000000 11972740514677 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623284629/5000000000 : ℝ)^275 ≤ (8628567594593/20000000000000 : ℝ)^211 := by
    have hnat : (2623284629 : ℕ)^275*20000000000000^211 ≤ 8628567594593^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623284629 5000000000 8628567594593 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135208027/250000000 : ℝ)^275 ≤ (44884421499919/100000000000000 : ℝ)^211 := by
    have hnat : (135208027 : ℕ)^275*100000000000000^211 ≤ 44884421499919^211*250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135208027 250000000 44884421499919 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-981054357/5000000000 : ℝ), (2623284629/5000000000 : ℝ), (135208027/250000000 : ℝ)] ![(11972740514677/100000000000000 : ℝ), (8628567594593/20000000000000 : ℝ), (44884421499919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-981054357/5000000000 : ℝ)|^275 ≤ (11972740514677/100000000000000 : ℝ)^211
        have hw : |(-981054357/5000000000 : ℝ)|=(981054357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623284629/5000000000 : ℝ)|^275 ≤ (8628567594593/20000000000000 : ℝ)^211
        have hw : |(2623284629/5000000000 : ℝ)|=(2623284629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135208027/250000000 : ℝ)|^275 ≤ (44884421499919/100000000000000 : ℝ)^211
        have hw : |(135208027/250000000 : ℝ)|=(135208027/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s4_5 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1326253659/2500000000 : ℝ)*x 0 + (-941361467/5000000000 : ℝ)*x 1 + (270416053/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326253659/2500000000 : ℝ)^275 ≤ (43770267450611/100000000000000 : ℝ)^211 := by
    have hnat : (1326253659 : ℕ)^275*100000000000000^211 ≤ 43770267450611^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326253659 2500000000 43770267450611 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941361467/5000000000 : ℝ)^275 ≤ (88635244141/781250000000 : ℝ)^211 := by
    have hnat : (941361467 : ℕ)^275*781250000000^211 ≤ 88635244141^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941361467 5000000000 88635244141 781250000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270416053/500000000 : ℝ)^275 ≤ (44884421283591/100000000000000 : ℝ)^211 := by
    have hnat : (270416053 : ℕ)^275*100000000000000^211 ≤ 44884421283591^211*500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270416053 500000000 44884421283591 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326253659/2500000000 : ℝ), (-941361467/5000000000 : ℝ), (270416053/500000000 : ℝ)] ![(43770267450611/100000000000000 : ℝ), (88635244141/781250000000 : ℝ), (44884421283591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326253659/2500000000 : ℝ)|^275 ≤ (43770267450611/100000000000000 : ℝ)^211
        have hw : |(1326253659/2500000000 : ℝ)|=(1326253659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-941361467/5000000000 : ℝ)|^275 ≤ (88635244141/781250000000 : ℝ)^211
        have hw : |(-941361467/5000000000 : ℝ)|=(941361467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270416053/500000000 : ℝ)|^275 ≤ (44884421283591/100000000000000 : ℝ)^211
        have hw : |(270416053/500000000 : ℝ)|=(270416053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s4_6 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2652507309/5000000000 : ℝ)*x 0 + (2704160543/5000000000 : ℝ)*x 1 + (-1882722923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652507309/5000000000 : ℝ)^275 ≤ (10942566814263/25000000000000 : ℝ)^211 := by
    have hnat : (2652507309 : ℕ)^275*25000000000000^211 ≤ 10942566814263^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652507309 5000000000 10942566814263 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704160543/5000000000 : ℝ)^275 ≤ (22442210782409/50000000000000 : ℝ)^211 := by
    have hnat : (2704160543 : ℕ)^275*50000000000000^211 ≤ 22442210782409^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704160543 5000000000 22442210782409 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1882722923/10000000000 : ℝ)^275 ≤ (1418163895457/12500000000000 : ℝ)^211 := by
    have hnat : (1882722923 : ℕ)^275*12500000000000^211 ≤ 1418163895457^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882722923 10000000000 1418163895457 12500000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652507309/5000000000 : ℝ), (2704160543/5000000000 : ℝ), (-1882722923/10000000000 : ℝ)] ![(10942566814263/25000000000000 : ℝ), (22442210782409/50000000000000 : ℝ), (1418163895457/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652507309/5000000000 : ℝ)|^275 ≤ (10942566814263/25000000000000 : ℝ)^211
        have hw : |(2652507309/5000000000 : ℝ)|=(2652507309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704160543/5000000000 : ℝ)|^275 ≤ (22442210782409/50000000000000 : ℝ)^211
        have hw : |(2704160543/5000000000 : ℝ)|=(2704160543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1882722923/10000000000 : ℝ)|^275 ≤ (1418163895457/12500000000000 : ℝ)^211
        have hw : |(-1882722923/10000000000 : ℝ)|=(1882722923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s4_7 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2150784667/5000000000 : ℝ)*x 0 + (4480472883/10000000000 : ℝ)*x 1 + (33033111/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150784667/5000000000 : ℝ)^275 ≤ (6660848343023/20000000000000 : ℝ)^211 := by
    have hnat : (2150784667 : ℕ)^275*20000000000000^211 ≤ 6660848343023^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150784667 5000000000 6660848343023 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480472883/10000000000 : ℝ)^275 ≤ (35120788979183/100000000000000 : ℝ)^211 := by
    have hnat : (4480472883 : ℕ)^275*100000000000000^211 ≤ 35120788979183^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480472883 10000000000 35120788979183 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33033111/80000000 : ℝ)^275 ≤ (31574969289887/100000000000000 : ℝ)^211 := by
    have hnat : (33033111 : ℕ)^275*100000000000000^211 ≤ 31574969289887^211*80000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33033111 80000000 31574969289887 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150784667/5000000000 : ℝ), (4480472883/10000000000 : ℝ), (33033111/80000000 : ℝ)] ![(6660848343023/20000000000000 : ℝ), (35120788979183/100000000000000 : ℝ), (31574969289887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150784667/5000000000 : ℝ)|^275 ≤ (6660848343023/20000000000000 : ℝ)^211
        have hw : |(2150784667/5000000000 : ℝ)|=(2150784667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480472883/10000000000 : ℝ)|^275 ≤ (35120788979183/100000000000000 : ℝ)^211
        have hw : |(4480472883/10000000000 : ℝ)|=(4480472883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33033111/80000000 : ℝ)|^275 ≤ (31574969289887/100000000000000 : ℝ)^211
        have hw : |(33033111/80000000 : ℝ)|=(33033111/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1440_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14941/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5597/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11337/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14789/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14941/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5597/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14941/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5597/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14941/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5597/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14941/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5597/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14941/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5597/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14941/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5597/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (5597/50000 : ℝ) ^ (4399/1024 : ℝ) ≤ (410683686311141/5000000000000000000 : ℝ) := by
    have hpowers : (5597/50000 : ℝ)^4399 ≤ (410683686311141/5000000000000000000 : ℝ)^1024 := by
      have hnat : (5597 : ℕ)^4399*5000000000000000000^1024 ≤ 410683686311141^1024*50000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5597 50000 410683686311141 5000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5597/50000 : ℝ)) (X := (410683686311141/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14941/100000 : ℝ) ^ (4399/1024 : ℝ) ≤ (7098374441623963/25000000000000000000 : ℝ) := by
    have hpowers : (14941/100000 : ℝ)^4399 ≤ (7098374441623963/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14941 : ℕ)^4399*25000000000000000000^1024 ≤ 7098374441623963^1024*100000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14941 100000 7098374441623963 25000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14941/100000 : ℝ)) (X := (7098374441623963/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500410683686311141/2500000000000000000 : ℝ) ≤ (500019118599509/500000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (2500410683686311141/2500000000000000000 : ℝ)^1024 ≤ (500019118599509/500000000000000 : ℝ)^4399 := by
      have hnat : (2500410683686311141 : ℕ)^1024*500000000000000^4399 ≤ 500019118599509^4399*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500410683686311141 2500000000000000000 500019118599509 500000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500019118599509/500000000000000 : ℝ)) (X := (2500410683686311141/2500000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252287948218294917/6250000000000000000 : ℝ) ≤ (10000852022747619/10000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (6252287948218294917/6250000000000000000 : ℝ)^1024 ≤ (10000852022747619/10000000000000000 : ℝ)^4399 := by
      have hnat : (6252287948218294917 : ℕ)^1024*10000000000000000^4399 ≤ 10000852022747619^4399*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252287948218294917 6250000000000000000 10000852022747619 10000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000852022747619/10000000000000000 : ℝ)) (X := (6252287948218294917/6250000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507098374441623963/12500000000000000000 : ℝ) ≤ (5000660836752529/5000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (12507098374441623963/12500000000000000000 : ℝ)^1024 ≤ (5000660836752529/5000000000000000 : ℝ)^4399 := by
      have hnat : (12507098374441623963 : ℕ)^1024*5000000000000000^4399 ≤ 5000660836752529^4399*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507098374441623963 12500000000000000000 5000660836752529 5000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000660836752529/5000000000000000 : ℝ)) (X := (12507098374441623963/12500000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(410683686311141/5000000000000000000 : ℝ) ≤ ((1170653693959051879/1170937500000000000 : ℝ)+2*(469650757439/374700000000000 : ℝ)*(5597/50000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (1170653693959051879/1170937500000000000 : ℝ)+2*(469650757439/374700000000000 : ℝ)*(5597/50000 : ℝ)=(500019118599509/500000000000000 : ℝ) by norm_num, show 1+2*(410683686311141/5000000000000000000 : ℝ)=(2500410683686311141/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7098374441623963/25000000000000000000 : ℝ)+(410683686311141/5000000000000000000 : ℝ) ≤ ((1170653693959051879/1170937500000000000 : ℝ)+(469650757439/374700000000000 : ℝ)*((14941/100000 : ℝ)+(5597/50000 : ℝ)))^(4399/1024 : ℝ) := by
    rw [show (1170653693959051879/1170937500000000000 : ℝ)+(469650757439/374700000000000 : ℝ)*((14941/100000 : ℝ)+(5597/50000 : ℝ))=(10000852022747619/10000000000000000 : ℝ) by norm_num, show 1+(7098374441623963/25000000000000000000 : ℝ)+(410683686311141/5000000000000000000 : ℝ)=(6252287948218294917/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7098374441623963/25000000000000000000 : ℝ) ≤ ((1170653693959051879/1170937500000000000 : ℝ)+2*(469650757439/374700000000000 : ℝ)*(14941/100000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (1170653693959051879/1170937500000000000 : ℝ)+2*(469650757439/374700000000000 : ℝ)*(14941/100000 : ℝ)=(5000660836752529/5000000000000000 : ℝ) by norm_num, show 1+2*(7098374441623963/25000000000000000000 : ℝ)=(12507098374441623963/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1170653693959051879/1170937500000000000 : ℝ)*(X 1 0+X 2 0)+(469650757439/374700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (5597/50000 : ℝ)) (hi := (14941/100000 : ℝ)) (c := (1170653693959051879/1170937500000000000 : ℝ)) (alpha := (469650757439/374700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1170653693959051879/1170937500000000000 : ℝ)*(X 0 1+X 2 1)+(469650757439/374700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (5597/50000 : ℝ)) (hi := (14941/100000 : ℝ)) (c := (1170653693959051879/1170937500000000000 : ℝ)) (alpha := (469650757439/374700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1170653693959051879/1170937500000000000 : ℝ)*(X 0 2+X 1 2)+(469650757439/374700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (5597/50000 : ℝ)) (hi := (14941/100000 : ℝ)) (c := (1170653693959051879/1170937500000000000 : ℝ)) (alpha := (469650757439/374700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-490524227/2500000000 : ℝ)*X 0 0+(67611519/125000000 : ℝ)*X 0 1+(2622986001/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347421973/10000000000 : ℝ)*X 1 0+(-204507193/1000000000 : ℝ)*X 1 1+(1311493049/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347422057/10000000000 : ℝ)*X 2 0+(2622986101/5000000000 : ℝ)*X 2 1+(-2045071809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075385941/2500000000 : ℝ)*X 0 0+(4127834921/10000000000 : ℝ)*X 0 1+(2240885037/5000000000 : ℝ)*X 0 2+(1075385941/2500000000 : ℝ)*X 1 0+(4127834921/10000000000 : ℝ)*X 1 1+(2240885037/5000000000 : ℝ)*X 1 2+(1075385941/2500000000 : ℝ)*X 2 0+(4127834921/10000000000 : ℝ)*X 2 1+(2240885037/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-981054357/5000000000 : ℝ)*X 0 0+(2623284629/5000000000 : ℝ)*X 0 1+(135208027/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326253659/2500000000 : ℝ)*X 1 0+(-941361467/5000000000 : ℝ)*X 1 1+(270416053/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652507309/5000000000 : ℝ)*X 2 0+(2704160543/5000000000 : ℝ)*X 2 1+(-1882722923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2150784667/5000000000 : ℝ)*X 0 0+(4480472883/10000000000 : ℝ)*X 0 1+(33033111/80000000 : ℝ)*X 0 2+(2150784667/5000000000 : ℝ)*X 1 0+(4480472883/10000000000 : ℝ)*X 1 1+(33033111/80000000 : ℝ)*X 1 2+(2150784667/5000000000 : ℝ)*X 2 0+(4480472883/10000000000 : ℝ)*X 2 1+(33033111/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99349289008075980542601339/9757812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (46740731/3125000000000 : ℝ)*(base19) + (352415369/25000000000000 : ℝ)*(base23) + (97560591/100000000000000 : ℝ)*(lower2) + (10062647/6250000000000 : ℝ)*(upper3) + (196694509/100000000000000 : ℝ)*(upper5) + (1120294647279189/25000000000000 : ℝ)*(major0) + (1120294647279189/25000000000000 : ℝ)*(major1) + (1120294647279189/25000000000000 : ℝ)*(major2) + (6136906384703639/100000000000000 : ℝ)*(sp0) + (383559131477911/6250000000000 : ℝ)*(sp1) + (1534236547422123/25000000000000 : ℝ)*(sp2) + (70634810539613/2500000000000 : ℝ)*(sp3) + (41214646329/100000000000000 : ℝ)*(sp4) + (4204478817/25000000000000 : ℝ)*(sp7) + (706352309874947/25000000000000 : ℝ)*(f.failure) + (383559224959373/6250000000000 : ℝ)*(f.sum) + (3669786975751/3122500000000000000000000000 : ℝ)*base66 + (66211369366709127/9757812500000000000000000000000 : ℝ)*base67 + (171672217787427877/9757812500000000000000000000000 : ℝ)*base69 + (30312640077940501/4878906250000000000000000000000 : ℝ)*base71 + (1195311590561/195156250000000000000000000 : ℝ)*base74 + (3479809664866793/152465820312500000000000000000 : ℝ)*base75 + (9908437731540563/2439453125000000000000000000000 : ℝ)*base77 + (11706372495762469/1219726562500000000000000000000 : ℝ)*base79 + (2903952590597/1561250000000000000000000000 : ℝ)*base81 + (1564839/500000000000000000000 : ℝ)*base90 + (1564839/500000000000000000000 : ℝ)*base92 + (1564839/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54391683752244618493320201/9757812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (874315629/100000000000000 : ℝ)*(base19) + (238883221/25000000000000 : ℝ)*(base23) + (103459487/100000000000000 : ℝ)*(upper3) + (23399759/50000000000000 : ℝ)*(lower4) + (119272677/100000000000000 : ℝ)*(upper5) + (2257150977816423/50000000000000 : ℝ)*(major0) + (2257150977816423/50000000000000 : ℝ)*(major1) + (2257150977816423/50000000000000 : ℝ)*(major2) + (703752527/4000000000000 : ℝ)*(sp1) + (19342169459/100000000000000 : ℝ)*(sp2) + (1545577502540187/25000000000000 : ℝ)*(sp4) + (772786442753993/12500000000000 : ℝ)*(sp5) + (1236457942491681/20000000000000 : ℝ)*(sp6) + (177893357206209/6250000000000 : ℝ)*(sp7) + (177893357206209/6250000000000 : ℝ)*(f.failure) + (1545577502540187/25000000000000 : ℝ)*(f.sum) + (7893567221041/3122500000000000000000000000 : ℝ)*base66 + (30763846067081343/9757812500000000000000000000000 : ℝ)*base68 + (63206544019393843/9757812500000000000000000000000 : ℝ)*base70 + (181433054695584561/19515625000000000000000000000000 : ℝ)*base72 + (1830428803043/1561250000000000000000000000 : ℝ)*base74 + (141263726987362593/9757812500000000000000000000000 : ℝ)*base76 + (134183673409740811/19515625000000000000000000000000 : ℝ)*base78 + (19559160390800093/9757812500000000000000000000000 : ℝ)*base80 + (181108053679/780625000000000000000000000 : ℝ)*base82 + (924333/125000000000000000000 : ℝ)*base90 + (924333/125000000000000000000 : ℝ)*base92 + (924333/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1440_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14941/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5597/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1440_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1440_s5_0 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1962222199/10000000000 : ℝ)*x 0 + (2703907911/5000000000 : ℝ)*x 1 + (1049398993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1962222199/10000000000 : ℝ)^275 ≤ (11973643047517/100000000000000 : ℝ)^211 := by
    have hnat : (1962222199 : ℕ)^275*100000000000000^211 ≤ 11973643047517^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962222199 10000000000 11973643047517 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703907911/5000000000 : ℝ)^275 ≤ (44878956496361/100000000000000 : ℝ)^211 := by
    have hnat : (2703907911 : ℕ)^275*100000000000000^211 ≤ 44878956496361^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703907911 5000000000 44878956496361 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049398993/2000000000 : ℝ)^275 ≤ (43147400439309/100000000000000 : ℝ)^211 := by
    have hnat : (1049398993 : ℕ)^275*100000000000000^211 ≤ 43147400439309^211*2000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049398993 2000000000 43147400439309 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1962222199/10000000000 : ℝ), (2703907911/5000000000 : ℝ), (1049398993/2000000000 : ℝ)] ![(11973643047517/100000000000000 : ℝ), (44878956496361/100000000000000 : ℝ), (43147400439309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1962222199/10000000000 : ℝ)|^275 ≤ (11973643047517/100000000000000 : ℝ)^211
        have hw : |(-1962222199/10000000000 : ℝ)|=(1962222199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703907911/5000000000 : ℝ)|^275 ≤ (44878956496361/100000000000000 : ℝ)^211
        have hw : |(2703907911/5000000000 : ℝ)|=(2703907911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049398993/2000000000 : ℝ)|^275 ≤ (43147400439309/100000000000000 : ℝ)^211
        have hw : |(1049398993/2000000000 : ℝ)|=(1049398993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s5_1 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5347135767/10000000000 : ℝ)*x 0 + (-255511717/1250000000 : ℝ)*x 1 + (262349753/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347135767/10000000000 : ℝ)^275 ≤ (22111877077187/50000000000000 : ℝ)^211 := by
    have hnat : (5347135767 : ℕ)^275*50000000000000^211 ≤ 22111877077187^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347135767 10000000000 22111877077187 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (255511717/1250000000 : ℝ)^275 ≤ (12628844375241/100000000000000 : ℝ)^211 := by
    have hnat : (255511717 : ℕ)^275*100000000000000^211 ≤ 12628844375241^211*1250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255511717 1250000000 12628844375241 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262349753/500000000 : ℝ)^275 ≤ (43147401457473/100000000000000 : ℝ)^211 := by
    have hnat : (262349753 : ℕ)^275*100000000000000^211 ≤ 43147401457473^211*500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262349753 500000000 43147401457473 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347135767/10000000000 : ℝ), (-255511717/1250000000 : ℝ), (262349753/500000000 : ℝ)] ![(22111877077187/50000000000000 : ℝ), (12628844375241/100000000000000 : ℝ), (43147401457473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347135767/10000000000 : ℝ)|^275 ≤ (22111877077187/50000000000000 : ℝ)^211
        have hw : |(5347135767/10000000000 : ℝ)|=(5347135767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-255511717/1250000000 : ℝ)|^275 ≤ (12628844375241/100000000000000 : ℝ)^211
        have hw : |(-255511717/1250000000 : ℝ)|=(255511717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262349753/500000000 : ℝ)|^275 ≤ (43147401457473/100000000000000 : ℝ)^211
        have hw : |(262349753/500000000 : ℝ)|=(262349753/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s5_2 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (66839197/125000000 : ℝ)*x 0 + (5246995151/10000000000 : ℝ)*x 1 + (-16352749/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66839197/125000000 : ℝ)^275 ≤ (1105593851973/2500000000000 : ℝ)^211 := by
    have hnat : (66839197 : ℕ)^275*2500000000000^211 ≤ 1105593851973^211*125000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66839197 125000000 1105593851973 2500000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246995151/10000000000 : ℝ)^275 ≤ (168544540753/390625000000 : ℝ)^211 := by
    have hnat : (5246995151 : ℕ)^275*390625000000^211 ≤ 168544540753^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246995151 10000000000 168544540753 390625000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16352749/80000000 : ℝ)^275 ≤ (252576869629/2000000000000 : ℝ)^211 := by
    have hnat : (16352749 : ℕ)^275*2000000000000^211 ≤ 252576869629^211*80000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16352749 80000000 252576869629 2000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66839197/125000000 : ℝ), (5246995151/10000000000 : ℝ), (-16352749/80000000 : ℝ)] ![(1105593851973/2500000000000 : ℝ), (168544540753/390625000000 : ℝ), (252576869629/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66839197/125000000 : ℝ)|^275 ≤ (1105593851973/2500000000000 : ℝ)^211
        have hw : |(66839197/125000000 : ℝ)|=(66839197/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246995151/10000000000 : ℝ)|^275 ≤ (168544540753/390625000000 : ℝ)^211
        have hw : |(5246995151/10000000000 : ℝ)|=(5246995151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16352749/80000000 : ℝ)|^275 ≤ (252576869629/2000000000000 : ℝ)^211
        have hw : |(-16352749/80000000 : ℝ)|=(16352749/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s5_3 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (860323817/2000000000 : ℝ)*x 0 + (4130138153/10000000000 : ℝ)*x 1 + (4479448841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860323817/2000000000 : ℝ)^275 ≤ (16652371870111/50000000000000 : ℝ)^211 := by
    have hnat : (860323817 : ℕ)^275*50000000000000^211 ≤ 16652371870111^211*2000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860323817 2000000000 16652371870111 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4130138153/10000000000 : ℝ)^275 ≤ (31584928753523/100000000000000 : ℝ)^211 := by
    have hnat : (4130138153 : ℕ)^275*100000000000000^211 ≤ 31584928753523^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130138153 10000000000 31584928753523 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479448841/10000000000 : ℝ)^275 ≤ (35110327493543/100000000000000 : ℝ)^211 := by
    have hnat : (4479448841 : ℕ)^275*100000000000000^211 ≤ 35110327493543^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479448841 10000000000 35110327493543 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860323817/2000000000 : ℝ), (4130138153/10000000000 : ℝ), (4479448841/10000000000 : ℝ)] ![(16652371870111/50000000000000 : ℝ), (31584928753523/100000000000000 : ℝ), (35110327493543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860323817/2000000000 : ℝ)|^275 ≤ (16652371870111/50000000000000 : ℝ)^211
        have hw : |(860323817/2000000000 : ℝ)|=(860323817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4130138153/10000000000 : ℝ)|^275 ≤ (31584928753523/100000000000000 : ℝ)^211
        have hw : |(4130138153/10000000000 : ℝ)|=(4130138153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479448841/10000000000 : ℝ)|^275 ≤ (35110327493543/100000000000000 : ℝ)^211
        have hw : |(4479448841/10000000000 : ℝ)|=(4479448841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s5_4 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-490558311/2500000000 : ℝ)*x 0 + (209903089/400000000 : ℝ)*x 1 + (5407230729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490558311/2500000000 : ℝ)^275 ≤ (11973730887947/100000000000000 : ℝ)^211 := by
    have hnat : (490558311 : ℕ)^275*100000000000000^211 ≤ 11973730887947^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490558311 2500000000 11973730887947 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209903089/400000000 : ℝ)^275 ≤ (43153640926429/100000000000000 : ℝ)^211 := by
    have hnat : (209903089 : ℕ)^275*100000000000000^211 ≤ 43153640926429^211*400000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209903089 400000000 43153640926429 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407230729/10000000000 : ℝ)^275 ≤ (8974525633987/20000000000000 : ℝ)^211 := by
    have hnat : (5407230729 : ℕ)^275*20000000000000^211 ≤ 8974525633987^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407230729 10000000000 8974525633987 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-490558311/2500000000 : ℝ), (209903089/400000000 : ℝ), (5407230729/10000000000 : ℝ)] ![(11973730887947/100000000000000 : ℝ), (43153640926429/100000000000000 : ℝ), (8974525633987/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-490558311/2500000000 : ℝ)|^275 ≤ (11973730887947/100000000000000 : ℝ)^211
        have hw : |(-490558311/2500000000 : ℝ)|=(490558311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209903089/400000000 : ℝ)|^275 ≤ (43153640926429/100000000000000 : ℝ)^211
        have hw : |(209903089/400000000 : ℝ)|=(209903089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407230729/10000000000 : ℝ)|^275 ≤ (8974525633987/20000000000000 : ℝ)^211
        have hw : |(5407230729/10000000000 : ℝ)|=(5407230729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s5_5 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (82895031/156250000 : ℝ)*x 0 + (-1883858383/10000000000 : ℝ)*x 1 + (5407230711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82895031/156250000 : ℝ)^275 ≤ (875462847061/2000000000000 : ℝ)^211 := by
    have hnat : (82895031 : ℕ)^275*2000000000000^211 ≤ 875462847061^211*156250000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82895031 156250000 875462847061 2000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1883858383/10000000000 : ℝ)^275 ≤ (14192787079/125000000000 : ℝ)^211 := by
    have hnat : (1883858383 : ℕ)^275*125000000000^211 ≤ 14192787079^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883858383 10000000000 14192787079 125000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407230711/10000000000 : ℝ)^275 ≤ (11218156993813/25000000000000 : ℝ)^211 := by
    have hnat : (5407230711 : ℕ)^275*25000000000000^211 ≤ 11218156993813^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407230711 10000000000 11218156993813 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82895031/156250000 : ℝ), (-1883858383/10000000000 : ℝ), (5407230711/10000000000 : ℝ)] ![(875462847061/2000000000000 : ℝ), (14192787079/125000000000 : ℝ), (11218156993813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82895031/156250000 : ℝ)|^275 ≤ (875462847061/2000000000000 : ℝ)^211
        have hw : |(82895031/156250000 : ℝ)|=(82895031/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1883858383/10000000000 : ℝ)|^275 ≤ (14192787079/125000000000 : ℝ)^211
        have hw : |(-1883858383/10000000000 : ℝ)|=(1883858383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407230711/10000000000 : ℝ)|^275 ≤ (11218156993813/25000000000000 : ℝ)^211
        have hw : |(5407230711/10000000000 : ℝ)|=(5407230711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s5_6 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1326320321/2500000000 : ℝ)*x 0 + (1081446307/2000000000 : ℝ)*x 1 + (-941929103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326320321/2500000000 : ℝ)^275 ≤ (21886567412803/50000000000000 : ℝ)^211 := by
    have hnat : (1326320321 : ℕ)^275*50000000000000^211 ≤ 21886567412803^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326320321 2500000000 21886567412803 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081446307/2000000000 : ℝ)^275 ≤ (22436318443717/50000000000000 : ℝ)^211 := by
    have hnat : (1081446307 : ℕ)^275*50000000000000^211 ≤ 22436318443717^211*2000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081446307 2000000000 22436318443717 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941929103/5000000000 : ℝ)^275 ≤ (5677114136411/50000000000000 : ℝ)^211 := by
    have hnat : (941929103 : ℕ)^275*50000000000000^211 ≤ 5677114136411^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941929103 5000000000 5677114136411 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326320321/2500000000 : ℝ), (1081446307/2000000000 : ℝ), (-941929103/5000000000 : ℝ)] ![(21886567412803/50000000000000 : ℝ), (22436318443717/50000000000000 : ℝ), (5677114136411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326320321/2500000000 : ℝ)|^275 ≤ (21886567412803/50000000000000 : ℝ)^211
        have hw : |(1326320321/2500000000 : ℝ)|=(1326320321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081446307/2000000000 : ℝ)|^275 ≤ (22436318443717/50000000000000 : ℝ)^211
        have hw : |(1081446307/2000000000 : ℝ)|=(1081446307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-941929103/5000000000 : ℝ)|^275 ≤ (5677114136411/50000000000000 : ℝ)^211
        have hw : |(-941929103/5000000000 : ℝ)|=(941929103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s5_7 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (430164373/1000000000 : ℝ)*x 0 + (559773201/1250000000 : ℝ)*x 1 + (2065703907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430164373/1000000000 : ℝ)^275 ≤ (33304992427509/100000000000000 : ℝ)^211 := by
    have hnat : (430164373 : ℕ)^275*100000000000000^211 ≤ 33304992427509^211*1000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430164373 1000000000 33304992427509 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559773201/1250000000 : ℝ)^275 ≤ (17548711730873/50000000000000 : ℝ)^211 := by
    have hnat : (559773201 : ℕ)^275*50000000000000^211 ≤ 17548711730873^211*1250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559773201 1250000000 17548711730873 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065703907/5000000000 : ℝ)^275 ≤ (3949698010849/12500000000000 : ℝ)^211 := by
    have hnat : (2065703907 : ℕ)^275*12500000000000^211 ≤ 3949698010849^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065703907 5000000000 3949698010849 12500000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430164373/1000000000 : ℝ), (559773201/1250000000 : ℝ), (2065703907/5000000000 : ℝ)] ![(33304992427509/100000000000000 : ℝ), (17548711730873/50000000000000 : ℝ), (3949698010849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430164373/1000000000 : ℝ)|^275 ≤ (33304992427509/100000000000000 : ℝ)^211
        have hw : |(430164373/1000000000 : ℝ)|=(430164373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559773201/1250000000 : ℝ)|^275 ≤ (17548711730873/50000000000000 : ℝ)^211
        have hw : |(559773201/1250000000 : ℝ)|=(559773201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2065703907/5000000000 : ℝ)|^275 ≤ (3949698010849/12500000000000 : ℝ)^211
        have hw : |(2065703907/5000000000 : ℝ)|=(2065703907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1440_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11359/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7383/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14789/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14789/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14789/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14789/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14789/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14789/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11337/100000 : ℝ) ^ (4399/1024 : ℝ) ≤ (8674012935686501/100000000000000000000 : ℝ) := by
    have hpowers : (11337/100000 : ℝ)^4399 ≤ (8674012935686501/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11337 : ℕ)^4399*100000000000000000000^1024 ≤ 8674012935686501^1024*100000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11337 100000 8674012935686501 100000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11337/100000 : ℝ)) (X := (8674012935686501/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14789/100000 : ℝ) ^ (4399/1024 : ℝ) ≤ (6793310026845277/25000000000000000000 : ℝ) := by
    have hpowers : (14789/100000 : ℝ)^4399 ≤ (6793310026845277/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14789 : ℕ)^4399*25000000000000000000^1024 ≤ 6793310026845277^1024*100000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14789 100000 6793310026845277 25000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14789/100000 : ℝ)) (X := (6793310026845277/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008674012935686501/50000000000000000000 : ℝ) ≤ (10000403800782359/10000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (50008674012935686501/50000000000000000000 : ℝ)^1024 ≤ (10000403800782359/10000000000000000 : ℝ)^4399 := by
      have hnat : (50008674012935686501 : ℕ)^1024*10000000000000000^4399 ≤ 10000403800782359^4399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008674012935686501 50000000000000000000 10000403800782359 10000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000403800782359/10000000000000000 : ℝ)) (X := (50008674012935686501/50000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035847253043067609/100000000000000000000 : ℝ) ≤ (10000834338267533/10000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (100035847253043067609/100000000000000000000 : ℝ)^1024 ≤ (10000834338267533/10000000000000000 : ℝ)^4399 := by
      have hnat : (100035847253043067609 : ℕ)^1024*10000000000000000^4399 ≤ 10000834338267533^4399*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035847253043067609 100000000000000000000 10000834338267533 10000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000834338267533/10000000000000000 : ℝ)) (X := (100035847253043067609/100000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506793310026845277/12500000000000000000 : ℝ) ≤ (10001264875752707/10000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (12506793310026845277/12500000000000000000 : ℝ)^1024 ≤ (10001264875752707/10000000000000000 : ℝ)^4399 := by
      have hnat : (12506793310026845277 : ℕ)^1024*10000000000000000^4399 ≤ 10001264875752707^4399*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506793310026845277 12500000000000000000 10001264875752707 10000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001264875752707/10000000000000000 : ℝ)) (X := (12506793310026845277/12500000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8674012935686501/100000000000000000000 : ℝ) ≤ ((4313953989170233499/4315000000000000000 : ℝ)+2*(215268742587/172600000000000 : ℝ)*(11337/100000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (4313953989170233499/4315000000000000000 : ℝ)+2*(215268742587/172600000000000 : ℝ)*(11337/100000 : ℝ)=(10000403800782359/10000000000000000 : ℝ) by norm_num, show 1+2*(8674012935686501/100000000000000000000 : ℝ)=(50008674012935686501/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6793310026845277/25000000000000000000 : ℝ)+(8674012935686501/100000000000000000000 : ℝ) ≤ ((4313953989170233499/4315000000000000000 : ℝ)+(215268742587/172600000000000 : ℝ)*((14789/100000 : ℝ)+(11337/100000 : ℝ)))^(4399/1024 : ℝ) := by
    rw [show (4313953989170233499/4315000000000000000 : ℝ)+(215268742587/172600000000000 : ℝ)*((14789/100000 : ℝ)+(11337/100000 : ℝ))=(10000834338267533/10000000000000000 : ℝ) by norm_num, show 1+(6793310026845277/25000000000000000000 : ℝ)+(8674012935686501/100000000000000000000 : ℝ)=(100035847253043067609/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6793310026845277/25000000000000000000 : ℝ) ≤ ((4313953989170233499/4315000000000000000 : ℝ)+2*(215268742587/172600000000000 : ℝ)*(14789/100000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (4313953989170233499/4315000000000000000 : ℝ)+2*(215268742587/172600000000000 : ℝ)*(14789/100000 : ℝ)=(10001264875752707/10000000000000000 : ℝ) by norm_num, show 1+2*(6793310026845277/25000000000000000000 : ℝ)=(12506793310026845277/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4313953989170233499/4315000000000000000 : ℝ)*(X 1 0+X 2 0)+(215268742587/172600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (4313953989170233499/4315000000000000000 : ℝ)) (alpha := (215268742587/172600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4313953989170233499/4315000000000000000 : ℝ)*(X 0 1+X 2 1)+(215268742587/172600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (4313953989170233499/4315000000000000000 : ℝ)) (alpha := (215268742587/172600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4313953989170233499/4315000000000000000 : ℝ)*(X 0 2+X 1 2)+(215268742587/172600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (4313953989170233499/4315000000000000000 : ℝ)) (alpha := (215268742587/172600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1962222199/10000000000 : ℝ)*X 0 0+(2703907911/5000000000 : ℝ)*X 0 1+(1049398993/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347135767/10000000000 : ℝ)*X 1 0+(-255511717/1250000000 : ℝ)*X 1 1+(262349753/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66839197/125000000 : ℝ)*X 2 0+(5246995151/10000000000 : ℝ)*X 2 1+(-16352749/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((860323817/2000000000 : ℝ)*X 0 0+(4130138153/10000000000 : ℝ)*X 0 1+(4479448841/10000000000 : ℝ)*X 0 2+(860323817/2000000000 : ℝ)*X 1 0+(4130138153/10000000000 : ℝ)*X 1 1+(4479448841/10000000000 : ℝ)*X 1 2+(860323817/2000000000 : ℝ)*X 2 0+(4130138153/10000000000 : ℝ)*X 2 1+(4479448841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-490558311/2500000000 : ℝ)*X 0 0+(209903089/400000000 : ℝ)*X 0 1+(5407230729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82895031/156250000 : ℝ)*X 1 0+(-1883858383/10000000000 : ℝ)*X 1 1+(5407230711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326320321/2500000000 : ℝ)*X 2 0+(1081446307/2000000000 : ℝ)*X 2 1+(-941929103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((430164373/1000000000 : ℝ)*X 0 0+(559773201/1250000000 : ℝ)*X 0 1+(2065703907/5000000000 : ℝ)*X 0 2+(430164373/1000000000 : ℝ)*X 1 0+(559773201/1250000000 : ℝ)*X 1 1+(2065703907/5000000000 : ℝ)*X 1 2+(430164373/1000000000 : ℝ)*X 2 0+(559773201/1250000000 : ℝ)*X 2 1+(2065703907/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48861074561140600820666673/6742187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (397667333/25000000000000 : ℝ)*(base19) + (191344367/12500000000000 : ℝ)*(base23) + (16923349/20000000000000 : ℝ)*(upper3) + (27684313/100000000000000 : ℝ)*(upper4) + (189036519/100000000000000 : ℝ)*(upper5) + (567562227659157/12500000000000 : ℝ)*(major0) + (567562227659157/12500000000000 : ℝ)*(major1) + (567562227659157/12500000000000 : ℝ)*(major2) + (97158428912429/1562500000000 : ℝ)*(sp0) + (1243636689784037/20000000000000 : ℝ)*(sp1) + (6218183508834581/100000000000000 : ℝ)*(sp2) + (143139815536593/5000000000000 : ℝ)*(sp3) + (2279459703/5000000000000 : ℝ)*(sp4) + (3512664069/25000000000000 : ℝ)*(sp7) + (357851295173517/12500000000000 : ℝ)*(f.failure) + (6218185039589517/100000000000000 : ℝ)*(f.sum) + (2186640681763/539375000000000000000000000 : ℝ)*base66 + (722339476644475343/53937500000000000000000000000000 : ℝ)*base67 + (134427774680024657/53937500000000000000000000000000 : ℝ)*base70 + (112595685609162843/53937500000000000000000000000000 : ℝ)*base71 + (1151319244727/539375000000000000000000000 : ℝ)*base73 + (590376943622475343/53937500000000000000000000000000 : ℝ)*base75 + (368908861178225343/53937500000000000000000000000000 : ℝ)*base77 + (954641363623412843/53937500000000000000000000000000 : ℝ)*base79 + (25643425191049/4315000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1930071/250000000000000000000 : ℝ)*base89 + (1930071/250000000000000000000 : ℝ)*base91 + (1930071/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1083333823414157688661514967/107875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (148807117/25000000000000 : ℝ)*(base19) + (28810451/50000000000000 : ℝ)*(lower2) + (262100317/100000000000000 : ℝ)*(upper3) + (121221291/100000000000000 : ℝ)*(lower4) + (6304099/100000000000000 : ℝ)*(upper5) + (2286810633336489/50000000000000 : ℝ)*(major0) + (2286810633336489/50000000000000 : ℝ)*(major1) + (2286810633336489/50000000000000 : ℝ)*(major2) + (7055689523/50000000000000 : ℝ)*(sp2) + (766652177/50000000000000 : ℝ)*(sp3) + (1252709462334387/20000000000000 : ℝ)*(sp4) + (6263546716443467/100000000000000 : ℝ)*(sp5) + (782941650036611/12500000000000 : ℝ)*(sp6) + (360461669202491/12500000000000 : ℝ)*(sp7) + (1441847443462141/50000000000000 : ℝ)*(f.failure) + (1252709462334387/20000000000000 : ℝ)*(f.sum) + (14710179925807/4315000000000000000000000000 : ℝ)*base66 + (902969438192829989/215750000000000000000000000000000 : ℝ)*base68 + (1126468490187170011/215750000000000000000000000000000 : ℝ)*base69 + (3208782994479420011/215750000000000000000000000000000 : ℝ)*base71 + (5654677972917/1078750000000000000000000000 : ℝ)*base73 + (202297878859329989/215750000000000000000000000000000 : ℝ)*base76 + (1099525854351420011/215750000000000000000000000000000 : ℝ)*base77 + (1095490740353920011/215750000000000000000000000000000 : ℝ)*base79 + (18446236760223/4315000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1705383/1000000000000000000000 : ℝ)*base89 + (1705383/1000000000000000000000 : ℝ)*base91 + (1705383/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1440_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1440_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1440_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (417/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1440_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1440_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1440_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (417/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1440_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
