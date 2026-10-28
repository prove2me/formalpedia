-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1279_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:22:23.863057+00:00
-- url     : https://prove2.me/submissions/f6124dbb-d403-4c95-a4e5-2da048fe0793

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
theorem support_rectangle_w1279_s0_0 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-369396737/2000000000 : ℝ)*x 0 + (3012286829/5000000000 : ℝ)*x 1 + (299728571/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (369396737/2000000000 : ℝ)^4239 ≤ (2696288867573/25000000000000 : ℝ)^3215 := by
    have hnat : (369396737 : ℕ)^4239*25000000000000^3215 ≤ 2696288867573^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369396737 2000000000 2696288867573 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3012286829/5000000000 : ℝ)^4239 ≤ (12816555411351/25000000000000 : ℝ)^3215 := by
    have hnat : (3012286829 : ℕ)^4239*25000000000000^3215 ≤ 12816555411351^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3012286829 5000000000 12816555411351 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299728571/625000000 : ℝ)^4239 ≤ (37948622872051/100000000000000 : ℝ)^3215 := by
    have hnat : (299728571 : ℕ)^4239*100000000000000^3215 ≤ 37948622872051^3215*625000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299728571 625000000 37948622872051 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-369396737/2000000000 : ℝ), (3012286829/5000000000 : ℝ), (299728571/625000000 : ℝ)] ![(2696288867573/25000000000000 : ℝ), (12816555411351/25000000000000 : ℝ), (37948622872051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-369396737/2000000000 : ℝ)|^4239 ≤ (2696288867573/25000000000000 : ℝ)^3215
        have hw : |(-369396737/2000000000 : ℝ)|=(369396737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3012286829/5000000000 : ℝ)|^4239 ≤ (12816555411351/25000000000000 : ℝ)^3215
        have hw : |(3012286829/5000000000 : ℝ)|=(3012286829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299728571/625000000 : ℝ)|^4239 ≤ (37948622872051/100000000000000 : ℝ)^3215
        have hw : |(299728571/625000000 : ℝ)|=(299728571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s0_1 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5508877791/10000000000 : ℝ)*x 0 + (-509751279/2000000000 : ℝ)*x 1 + (1198914277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5508877791/10000000000 : ℝ)^4239 ≤ (4556065251917/10000000000000 : ℝ)^3215 := by
    have hnat : (5508877791 : ℕ)^4239*10000000000000^3215 ≤ 4556065251917^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508877791 10000000000 4556065251917 10000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509751279/2000000000 : ℝ)^4239 ≤ (8245362440473/50000000000000 : ℝ)^3215 := by
    have hnat : (509751279 : ℕ)^4239*50000000000000^3215 ≤ 8245362440473^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509751279 2000000000 8245362440473 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198914277/2500000000 : ℝ)^4239 ≤ (4743577822489/12500000000000 : ℝ)^3215 := by
    have hnat : (1198914277 : ℕ)^4239*12500000000000^3215 ≤ 4743577822489^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198914277 2500000000 4743577822489 12500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5508877791/10000000000 : ℝ), (-509751279/2000000000 : ℝ), (1198914277/2500000000 : ℝ)] ![(4556065251917/10000000000000 : ℝ), (8245362440473/50000000000000 : ℝ), (4743577822489/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5508877791/10000000000 : ℝ)|^4239 ≤ (4556065251917/10000000000000 : ℝ)^3215
        have hw : |(5508877791/10000000000 : ℝ)|=(5508877791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509751279/2000000000 : ℝ)|^4239 ≤ (8245362440473/50000000000000 : ℝ)^3215
        have hw : |(-509751279/2000000000 : ℝ)|=(509751279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198914277/2500000000 : ℝ)|^4239 ≤ (4743577822489/12500000000000 : ℝ)^3215
        have hw : |(1198914277/2500000000 : ℝ)|=(1198914277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s0_2 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5508877809/10000000000 : ℝ)*x 0 + (4795657109/10000000000 : ℝ)*x 1 + (-254875637/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5508877809/10000000000 : ℝ)^4239 ≤ (45560652715453/100000000000000 : ℝ)^3215 := by
    have hnat : (5508877809 : ℕ)^4239*100000000000000^3215 ≤ 45560652715453^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508877809 10000000000 45560652715453 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4795657109/10000000000 : ℝ)^4239 ≤ (18974311295173/50000000000000 : ℝ)^3215 := by
    have hnat : (4795657109 : ℕ)^4239*50000000000000^3215 ≤ 18974311295173^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795657109 10000000000 18974311295173 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254875637/1000000000 : ℝ)^4239 ≤ (8245362333837/50000000000000 : ℝ)^3215 := by
    have hnat : (254875637 : ℕ)^4239*50000000000000^3215 ≤ 8245362333837^3215*1000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254875637 1000000000 8245362333837 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5508877809/10000000000 : ℝ), (4795657109/10000000000 : ℝ), (-254875637/1000000000 : ℝ)] ![(45560652715453/100000000000000 : ℝ), (18974311295173/50000000000000 : ℝ), (8245362333837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5508877809/10000000000 : ℝ)|^4239 ≤ (45560652715453/100000000000000 : ℝ)^3215
        have hw : |(5508877809/10000000000 : ℝ)|=(5508877809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4795657109/10000000000 : ℝ)|^4239 ≤ (18974311295173/50000000000000 : ℝ)^3215
        have hw : |(4795657109/10000000000 : ℝ)|=(4795657109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254875637/1000000000 : ℝ)|^4239 ≤ (8245362333837/50000000000000 : ℝ)^3215
        have hw : |(-254875637/1000000000 : ℝ)|=(254875637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s0_3 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4188337327/10000000000 : ℝ)*x 0 + (3110310843/10000000000 : ℝ)*x 1 + (2811742647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4188337327/10000000000 : ℝ)^4239 ≤ (31743826256807/100000000000000 : ℝ)^3215 := by
    have hnat : (4188337327 : ℕ)^4239*100000000000000^3215 ≤ 31743826256807^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188337327 10000000000 31743826256807 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3110310843/10000000000 : ℝ)^4239 ≤ (10720826252137/50000000000000 : ℝ)^3215 := by
    have hnat : (3110310843 : ℕ)^4239*50000000000000^3215 ≤ 10720826252137^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110310843 10000000000 10720826252137 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2811742647/5000000000 : ℝ)^4239 ≤ (46814521230321/100000000000000 : ℝ)^3215 := by
    have hnat : (2811742647 : ℕ)^4239*100000000000000^3215 ≤ 46814521230321^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2811742647 5000000000 46814521230321 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4188337327/10000000000 : ℝ), (3110310843/10000000000 : ℝ), (2811742647/5000000000 : ℝ)] ![(31743826256807/100000000000000 : ℝ), (10720826252137/50000000000000 : ℝ), (46814521230321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4188337327/10000000000 : ℝ)|^4239 ≤ (31743826256807/100000000000000 : ℝ)^3215
        have hw : |(4188337327/10000000000 : ℝ)|=(4188337327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3110310843/10000000000 : ℝ)|^4239 ≤ (10720826252137/50000000000000 : ℝ)^3215
        have hw : |(3110310843/10000000000 : ℝ)|=(3110310843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2811742647/5000000000 : ℝ)|^4239 ≤ (46814521230321/100000000000000 : ℝ)^3215
        have hw : |(2811742647/5000000000 : ℝ)|=(2811742647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s0_4 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1851779619/10000000000 : ℝ)*x 0 + (4827393749/10000000000 : ℝ)*x 1 + (5991709299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1851779619/10000000000 : ℝ)^4239 ≤ (10822095601657/100000000000000 : ℝ)^3215 := by
    have hnat : (1851779619 : ℕ)^4239*100000000000000^3215 ≤ 10822095601657^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851779619 10000000000 10822095601657 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4827393749/10000000000 : ℝ)^4239 ≤ (19140047756501/50000000000000 : ℝ)^3215 := by
    have hnat : (4827393749 : ℕ)^4239*50000000000000^3215 ≤ 19140047756501^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827393749 10000000000 19140047756501 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5991709299/10000000000 : ℝ)^4239 ≤ (50897808873719/100000000000000 : ℝ)^3215 := by
    have hnat : (5991709299 : ℕ)^4239*100000000000000^3215 ≤ 50897808873719^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5991709299 10000000000 50897808873719 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1851779619/10000000000 : ℝ), (4827393749/10000000000 : ℝ), (5991709299/10000000000 : ℝ)] ![(10822095601657/100000000000000 : ℝ), (19140047756501/50000000000000 : ℝ), (50897808873719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1851779619/10000000000 : ℝ)|^4239 ≤ (10822095601657/100000000000000 : ℝ)^3215
        have hw : |(-1851779619/10000000000 : ℝ)|=(1851779619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4827393749/10000000000 : ℝ)|^4239 ≤ (19140047756501/50000000000000 : ℝ)^3215
        have hw : |(4827393749/10000000000 : ℝ)|=(4827393749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5991709299/10000000000 : ℝ)|^4239 ≤ (50897808873719/100000000000000 : ℝ)^3215
        have hw : |(5991709299/10000000000 : ℝ)|=(5991709299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s0_5 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2587207431/5000000000 : ℝ)*x 0 + (-676350897/5000000000 : ℝ)*x 1 + (748963973/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587207431/5000000000 : ℝ)^4239 ≤ (41949235435963/100000000000000 : ℝ)^3215 := by
    have hnat : (2587207431 : ℕ)^4239*100000000000000^3215 ≤ 41949235435963^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587207431 5000000000 41949235435963 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676350897/5000000000 : ℝ)^4239 ≤ (35764639197/500000000000 : ℝ)^3215 := by
    have hnat : (676350897 : ℕ)^4239*500000000000^3215 ≤ 35764639197^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676350897 5000000000 35764639197 500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748963973/1250000000 : ℝ)^4239 ≤ (50897836706539/100000000000000 : ℝ)^3215 := by
    have hnat : (748963973 : ℕ)^4239*100000000000000^3215 ≤ 50897836706539^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748963973 1250000000 50897836706539 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587207431/5000000000 : ℝ), (-676350897/5000000000 : ℝ), (748963973/1250000000 : ℝ)] ![(41949235435963/100000000000000 : ℝ), (35764639197/500000000000 : ℝ), (50897836706539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587207431/5000000000 : ℝ)|^4239 ≤ (41949235435963/100000000000000 : ℝ)^3215
        have hw : |(2587207431/5000000000 : ℝ)|=(2587207431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-676350897/5000000000 : ℝ)|^4239 ≤ (35764639197/500000000000 : ℝ)^3215
        have hw : |(-676350897/5000000000 : ℝ)|=(676350897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(748963973/1250000000 : ℝ)|^4239 ≤ (50897836706539/100000000000000 : ℝ)^3215
        have hw : |(748963973/1250000000 : ℝ)|=(748963973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s0_6 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103488321/200000000 : ℝ)*x 0 + (2995854859/5000000000 : ℝ)*x 1 + (-1352703291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103488321/200000000 : ℝ)^4239 ≤ (20974624067367/50000000000000 : ℝ)^3215 := by
    have hnat : (103488321 : ℕ)^4239*50000000000000^3215 ≤ 20974624067367^3215*200000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103488321 200000000 20974624067367 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2995854859/5000000000 : ℝ)^4239 ≤ (50897813566657/100000000000000 : ℝ)^3215 := by
    have hnat : (2995854859 : ℕ)^4239*100000000000000^3215 ≤ 50897813566657^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2995854859 5000000000 50897813566657 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352703291/10000000000 : ℝ)^4239 ≤ (143058765533/2000000000000 : ℝ)^3215 := by
    have hnat : (1352703291 : ℕ)^4239*2000000000000^3215 ≤ 143058765533^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352703291 10000000000 143058765533 2000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103488321/200000000 : ℝ), (2995854859/5000000000 : ℝ), (-1352703291/10000000000 : ℝ)] ![(20974624067367/50000000000000 : ℝ), (50897813566657/100000000000000 : ℝ), (143058765533/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103488321/200000000 : ℝ)|^4239 ≤ (20974624067367/50000000000000 : ℝ)^3215
        have hw : |(103488321/200000000 : ℝ)|=(103488321/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2995854859/5000000000 : ℝ)|^4239 ≤ (50897813566657/100000000000000 : ℝ)^3215
        have hw : |(2995854859/5000000000 : ℝ)|=(2995854859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1352703291/10000000000 : ℝ)|^4239 ≤ (143058765533/2000000000000 : ℝ)^3215
        have hw : |(-1352703291/10000000000 : ℝ)|=(1352703291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s0_7 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (839629789/2000000000 : ℝ)*x 0 + (43426479/78125000 : ℝ)*x 1 + (3177513157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839629789/2000000000 : ℝ)^4239 ≤ (3980238907111/12500000000000 : ℝ)^3215 := by
    have hnat : (839629789 : ℕ)^4239*12500000000000^3215 ≤ 3980238907111^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839629789 2000000000 3980238907111 12500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43426479/78125000 : ℝ)^4239 ≤ (46103513573513/100000000000000 : ℝ)^3215 := by
    have hnat : (43426479 : ℕ)^4239*100000000000000^3215 ≤ 46103513573513^3215*78125000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43426479 78125000 46103513573513 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3177513157/10000000000 : ℝ)^4239 ≤ (4410915031153/20000000000000 : ℝ)^3215 := by
    have hnat : (3177513157 : ℕ)^4239*20000000000000^3215 ≤ 4410915031153^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3177513157 10000000000 4410915031153 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839629789/2000000000 : ℝ), (43426479/78125000 : ℝ), (3177513157/10000000000 : ℝ)] ![(3980238907111/12500000000000 : ℝ), (46103513573513/100000000000000 : ℝ), (4410915031153/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839629789/2000000000 : ℝ)|^4239 ≤ (3980238907111/12500000000000 : ℝ)^3215
        have hw : |(839629789/2000000000 : ℝ)|=(839629789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43426479/78125000 : ℝ)|^4239 ≤ (46103513573513/100000000000000 : ℝ)^3215
        have hw : |(43426479/78125000 : ℝ)|=(43426479/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3177513157/10000000000 : ℝ)|^4239 ≤ (4410915031153/20000000000000 : ℝ)^3215
        have hw : |(3177513157/10000000000 : ℝ)|=(3177513157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1279_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (931/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27331/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (2119/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2119 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2119*1^512 ≤ 0^512*1^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2119/512 : ℝ) ≤ (112726723102534847/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2119 ≤ (112726723102534847/5000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2119*5000000000000000000^512 ≤ 112726723102534847^512*5^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 112726723102534847 5000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (112726723102534847/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2119 := by
      have hnat : (1 : ℕ)^512*1^2119 ≤ 1^2119*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5112726723102534847/5000000000000000000 : ℝ) ≤ (10054015188184499/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (5112726723102534847/5000000000000000000 : ℝ)^512 ≤ (10054015188184499/10000000000000000 : ℝ)^2119 := by
      have hnat : (5112726723102534847 : ℕ)^512*10000000000000000^2119 ≤ 10054015188184499^2119*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5112726723102534847 5000000000000000000 10054015188184499 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10054015188184499/10000000000000000 : ℝ)) (X := (5112726723102534847/5000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2612726723102534847/2500000000000000000 : ℝ) ≤ (5054015188184499/5000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (2612726723102534847/2500000000000000000 : ℝ)^512 ≤ (5054015188184499/5000000000000000 : ℝ)^2119 := by
      have hnat : (2612726723102534847 : ℕ)^512*5000000000000000^2119 ≤ 5054015188184499^2119*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2612726723102534847 2500000000000000000 5054015188184499 5000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054015188184499/5000000000000000 : ℝ)) (X := (2612726723102534847/2500000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(54015188184499/4000000000000000 : ℝ)*(0 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(54015188184499/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(112726723102534847/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(54015188184499/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2119/512 : ℝ) := by
    rw [show (1 : ℝ)+(54015188184499/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10054015188184499/10000000000000000 : ℝ) by norm_num, show 1+(112726723102534847/5000000000000000000 : ℝ)+(0 : ℝ)=(5112726723102534847/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(112726723102534847/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(54015188184499/4000000000000000 : ℝ)*(2/5 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(54015188184499/4000000000000000 : ℝ)*(2/5 : ℝ)=(5054015188184499/5000000000000000 : ℝ) by norm_num, show 1+2*(112726723102534847/5000000000000000000 : ℝ)=(2612726723102534847/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(54015188184499/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54015188184499/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(54015188184499/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54015188184499/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(54015188184499/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54015188184499/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-369396737/2000000000 : ℝ)*X 0 0+(3012286829/5000000000 : ℝ)*X 0 1+(299728571/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5508877791/10000000000 : ℝ)*X 1 0+(-509751279/2000000000 : ℝ)*X 1 1+(1198914277/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5508877809/10000000000 : ℝ)*X 2 0+(4795657109/10000000000 : ℝ)*X 2 1+(-254875637/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4188337327/10000000000 : ℝ)*X 0 0+(3110310843/10000000000 : ℝ)*X 0 1+(2811742647/5000000000 : ℝ)*X 0 2+(4188337327/10000000000 : ℝ)*X 1 0+(3110310843/10000000000 : ℝ)*X 1 1+(2811742647/5000000000 : ℝ)*X 1 2+(4188337327/10000000000 : ℝ)*X 2 0+(3110310843/10000000000 : ℝ)*X 2 1+(2811742647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1851779619/10000000000 : ℝ)*X 0 0+(4827393749/10000000000 : ℝ)*X 0 1+(5991709299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587207431/5000000000 : ℝ)*X 1 0+(-676350897/5000000000 : ℝ)*X 1 1+(748963973/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((103488321/200000000 : ℝ)*X 2 0+(2995854859/5000000000 : ℝ)*X 2 1+(-1352703291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((839629789/2000000000 : ℝ)*X 0 0+(43426479/78125000 : ℝ)*X 0 1+(3177513157/10000000000 : ℝ)*X 0 2+(839629789/2000000000 : ℝ)*X 1 0+(43426479/78125000 : ℝ)*X 1 1+(3177513157/10000000000 : ℝ)*X 1 2+(839629789/2000000000 : ℝ)*X 2 0+(43426479/78125000 : ℝ)*X 2 1+(3177513157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (356474155577470733163633/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21467087/50000000000000 : ℝ)*(base1) + (866989313/100000000000000 : ℝ)*(base19) + (173929627/20000000000000 : ℝ)*(base23) + (12227243/12500000000000 : ℝ)*(upper3) + (10477979/10000000000000 : ℝ)*(upper5) + (302909024900711/50000000000000 : ℝ)*(major0) + (302909024900711/50000000000000 : ℝ)*(major1) + (302909024900711/50000000000000 : ℝ)*(major2) + (406863747323709/50000000000000 : ℝ)*(sp0) + (813729348188859/100000000000000 : ℝ)*(sp1) + (203432336382509/25000000000000 : ℝ)*(sp2) + (397904404054961/100000000000000 : ℝ)*(sp3) + (86358279/3125000000000 : ℝ)*(sp4) + (263722163/20000000000000 : ℝ)*(sp7) + (7958115311999/2000000000000 : ℝ)*(f.failure) + (813730215178171/100000000000000 : ℝ)*(f.sum) + (217324658278789/100000000000000000000000000000 : ℝ)*base65 + (37923520478789/200000000000000000000000000000 : ℝ)*base67 + (855791537521211/200000000000000000000000000000 : ℝ)*base70 + (320296153921211/200000000000000000000000000000 : ℝ)*base72 + (471299014478789/100000000000000000000000000000 : ℝ)*base73 + (875015427921211/200000000000000000000000000000 : ℝ)*base76 + (230775715078789/200000000000000000000000000000 : ℝ)*base77 + (1032328358878789/200000000000000000000000000000 : ℝ)*base79 + (51306892621211/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (116361/200000000000000000000 : ℝ)*base89 + (116361/200000000000000000000 : ℝ)*base91 + (116361/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8732751982078167681009/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (241771713/100000000000000 : ℝ)*(base1) + (104312663/100000000000000 : ℝ)*(base19) + (58598263/20000000000000 : ℝ)*(base23) + (189377/781250000000 : ℝ)*(base59) + (79928362699253/12500000000000 : ℝ)*(major0) + (79928362699253/12500000000000 : ℝ)*(major1) + (79928362699253/12500000000000 : ℝ)*(major2) + (922859079/100000000000000 : ℝ)*(sp1) + (33217403/50000000000000 : ℝ)*(sp2) + (184958921/20000000000000 : ℝ)*(sp3) + (858873690919209/100000000000000 : ℝ)*(sp4) + (429436210987877/50000000000000 : ℝ)*(sp5) + (26839784053793/3125000000000 : ℝ)*(sp6) + (8399582817991/2000000000000 : ℝ)*(sp7) + (104995076866467/25000000000000 : ℝ)*(f.failure) + (107359181143437/12500000000000 : ℝ)*(f.sum) + (53459358129247/25000000000000000000000000000 : ℝ)*base65 + (252962405679247/50000000000000000000000000000 : ℝ)*base67 + (313672077929247/50000000000000000000000000000 : ℝ)*base69 + (164230912379247/50000000000000000000000000000 : ℝ)*base71 + (5502995129247/25000000000000000000000000000 : ℝ)*base73 + (250184869079247/50000000000000000000000000000 : ℝ)*base75 + (90470808470753/50000000000000000000000000000 : ℝ)*base78 + (76029758370753/50000000000000000000000000000 : ℝ)*base80 + (52295323879247/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15110587/2500000000000000000000 : ℝ)*base90 + (15110587/2500000000000000000000 : ℝ)*base92 + (15110587/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1279_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (931/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27331/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1279_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1279_s1_0 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2040914177/10000000000 : ℝ)*x 0 + (708947091/1250000000 : ℝ)*x 1 + (251225109/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040914177/10000000000 : ℝ)^4239 ≤ (3075665502227/25000000000000 : ℝ)^3215 := by
    have hnat : (2040914177 : ℕ)^4239*25000000000000^3215 ≤ 3075665502227^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040914177 10000000000 3075665502227 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708947091/1250000000 : ℝ)^4239 ≤ (37874485259/80000000000 : ℝ)^3215 := by
    have hnat : (708947091 : ℕ)^4239*80000000000^3215 ≤ 37874485259^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708947091 1250000000 37874485259 80000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251225109/500000000 : ℝ)^4239 ≤ (1614169256063/4000000000000 : ℝ)^3215 := by
    have hnat : (251225109 : ℕ)^4239*4000000000000^3215 ≤ 1614169256063^3215*500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251225109 500000000 1614169256063 4000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2040914177/10000000000 : ℝ), (708947091/1250000000 : ℝ), (251225109/500000000 : ℝ)] ![(3075665502227/25000000000000 : ℝ), (37874485259/80000000000 : ℝ), (1614169256063/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2040914177/10000000000 : ℝ)|^4239 ≤ (3075665502227/25000000000000 : ℝ)^3215
        have hw : |(-2040914177/10000000000 : ℝ)|=(2040914177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(708947091/1250000000 : ℝ)|^4239 ≤ (37874485259/80000000000 : ℝ)^3215
        have hw : |(708947091/1250000000 : ℝ)|=(708947091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251225109/500000000 : ℝ)|^4239 ≤ (1614169256063/4000000000000 : ℝ)^3215
        have hw : |(251225109/500000000 : ℝ)|=(251225109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s1_1 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1353092009/2500000000 : ℝ)*x 0 + (-2388150773/10000000000 : ℝ)*x 1 + (2512251011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353092009/2500000000 : ℝ)^4239 ≤ (2225560069013/5000000000000 : ℝ)^3215 := by
    have hnat : (1353092009 : ℕ)^4239*5000000000000^3215 ≤ 2225560069013^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353092009 2500000000 2225560069013 5000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2388150773/10000000000 : ℝ)^4239 ≤ (151345688781/1000000000000 : ℝ)^3215 := by
    have hnat : (2388150773 : ℕ)^4239*1000000000000^3215 ≤ 151345688781^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388150773 10000000000 151345688781 1000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512251011/5000000000 : ℝ)^4239 ≤ (20177114864211/50000000000000 : ℝ)^3215 := by
    have hnat : (2512251011 : ℕ)^4239*50000000000000^3215 ≤ 20177114864211^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512251011 5000000000 20177114864211 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353092009/2500000000 : ℝ), (-2388150773/10000000000 : ℝ), (2512251011/5000000000 : ℝ)] ![(2225560069013/5000000000000 : ℝ), (151345688781/1000000000000 : ℝ), (20177114864211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353092009/2500000000 : ℝ)|^4239 ≤ (2225560069013/5000000000000 : ℝ)^3215
        have hw : |(1353092009/2500000000 : ℝ)|=(1353092009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2388150773/10000000000 : ℝ)|^4239 ≤ (151345688781/1000000000000 : ℝ)^3215
        have hw : |(-2388150773/10000000000 : ℝ)|=(2388150773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2512251011/5000000000 : ℝ)|^4239 ≤ (20177114864211/50000000000000 : ℝ)^3215
        have hw : |(2512251011/5000000000 : ℝ)|=(2512251011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s1_2 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5412367841/10000000000 : ℝ)*x 0 + (1004900437/2000000000 : ℝ)*x 1 + (-2388150819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412367841/10000000000 : ℝ)^4239 ≤ (22255599632901/50000000000000 : ℝ)^3215 := by
    have hnat : (5412367841 : ℕ)^4239*50000000000000^3215 ≤ 22255599632901^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412367841 10000000000 22255599632901 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004900437/2000000000 : ℝ)^4239 ≤ (40354231454523/100000000000000 : ℝ)^3215 := by
    have hnat : (1004900437 : ℕ)^4239*100000000000000^3215 ≤ 40354231454523^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004900437 2000000000 40354231454523 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388150819/10000000000 : ℝ)^4239 ≤ (15134569262469/100000000000000 : ℝ)^3215 := by
    have hnat : (2388150819 : ℕ)^4239*100000000000000^3215 ≤ 15134569262469^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388150819 10000000000 15134569262469 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412367841/10000000000 : ℝ), (1004900437/2000000000 : ℝ), (-2388150819/10000000000 : ℝ)] ![(22255599632901/50000000000000 : ℝ), (40354231454523/100000000000000 : ℝ), (15134569262469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412367841/10000000000 : ℝ)|^4239 ≤ (22255599632901/50000000000000 : ℝ)^3215
        have hw : |(5412367841/10000000000 : ℝ)|=(5412367841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004900437/2000000000 : ℝ)|^4239 ≤ (40354231454523/100000000000000 : ℝ)^3215
        have hw : |(1004900437/2000000000 : ℝ)|=(1004900437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2388150819/10000000000 : ℝ)|^4239 ≤ (15134569262469/100000000000000 : ℝ)^3215
        have hw : |(-2388150819/10000000000 : ℝ)|=(2388150819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s1_3 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151706643/5000000000 : ℝ)*x 0 + (369023487/1000000000 : ℝ)*x 1 + (1253380867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151706643/5000000000 : ℝ)^4239 ≤ (3289879203873/10000000000000 : ℝ)^3215 := by
    have hnat : (2151706643 : ℕ)^4239*10000000000000^3215 ≤ 3289879203873^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151706643 5000000000 3289879203873 10000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369023487/1000000000 : ℝ)^4239 ≤ (3357899493737/12500000000000 : ℝ)^3215 := by
    have hnat : (369023487 : ℕ)^4239*12500000000000^3215 ≤ 3357899493737^3215*1000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369023487 1000000000 3357899493737 12500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1253380867/2500000000 : ℝ)^4239 ≤ (40238011996457/100000000000000 : ℝ)^3215 := by
    have hnat : (1253380867 : ℕ)^4239*100000000000000^3215 ≤ 40238011996457^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253380867 2500000000 40238011996457 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151706643/5000000000 : ℝ), (369023487/1000000000 : ℝ), (1253380867/2500000000 : ℝ)] ![(3289879203873/10000000000000 : ℝ), (3357899493737/12500000000000 : ℝ), (40238011996457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151706643/5000000000 : ℝ)|^4239 ≤ (3289879203873/10000000000000 : ℝ)^3215
        have hw : |(2151706643/5000000000 : ℝ)|=(2151706643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(369023487/1000000000 : ℝ)|^4239 ≤ (3357899493737/12500000000000 : ℝ)^3215
        have hw : |(369023487/1000000000 : ℝ)|=(369023487/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1253380867/2500000000 : ℝ)|^4239 ≤ (40238011996457/100000000000000 : ℝ)^3215
        have hw : |(1253380867/2500000000 : ℝ)|=(1253380867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s1_4 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-255197499/1250000000 : ℝ)*x 0 + (5033021883/10000000000 : ℝ)*x 1 + (5662894323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (255197499/1250000000 : ℝ)^4239 ≤ (6153977084209/50000000000000 : ℝ)^3215 := by
    have hnat : (255197499 : ℕ)^4239*50000000000000^3215 ≤ 6153977084209^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255197499 1250000000 6153977084209 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5033021883/10000000000 : ℝ)^4239 ≤ (10111118944561/25000000000000 : ℝ)^3215 := by
    have hnat : (5033021883 : ℕ)^4239*25000000000000^3215 ≤ 10111118944561^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033021883 10000000000 10111118944561 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5662894323/10000000000 : ℝ)^4239 ≤ (47247570037601/100000000000000 : ℝ)^3215 := by
    have hnat : (5662894323 : ℕ)^4239*100000000000000^3215 ≤ 47247570037601^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662894323 10000000000 47247570037601 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-255197499/1250000000 : ℝ), (5033021883/10000000000 : ℝ), (5662894323/10000000000 : ℝ)] ![(6153977084209/50000000000000 : ℝ), (10111118944561/25000000000000 : ℝ), (47247570037601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-255197499/1250000000 : ℝ)|^4239 ≤ (6153977084209/50000000000000 : ℝ)^3215
        have hw : |(-255197499/1250000000 : ℝ)|=(255197499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5033021883/10000000000 : ℝ)|^4239 ≤ (10111118944561/25000000000000 : ℝ)^3215
        have hw : |(5033021883/10000000000 : ℝ)|=(5033021883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5662894323/10000000000 : ℝ)|^4239 ≤ (47247570037601/100000000000000 : ℝ)^3215
        have hw : |(5662894323/10000000000 : ℝ)|=(5662894323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s1_5 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5245382579/10000000000 : ℝ)*x 0 + (-874879203/5000000000 : ℝ)*x 1 + (2831447357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245382579/10000000000 : ℝ)^4239 ≤ (21354737694169/50000000000000 : ℝ)^3215 := by
    have hnat : (5245382579 : ℕ)^4239*50000000000000^3215 ≤ 21354737694169^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245382579 10000000000 21354737694169 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874879203/5000000000 : ℝ)^4239 ≤ (10042950261447/100000000000000 : ℝ)^3215 := by
    have hnat : (874879203 : ℕ)^4239*100000000000000^3215 ≤ 10042950261447^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874879203 5000000000 10042950261447 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2831447357/5000000000 : ℝ)^4239 ≤ (23623787169453/50000000000000 : ℝ)^3215 := by
    have hnat : (2831447357 : ℕ)^4239*50000000000000^3215 ≤ 23623787169453^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831447357 5000000000 23623787169453 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245382579/10000000000 : ℝ), (-874879203/5000000000 : ℝ), (2831447357/5000000000 : ℝ)] ![(21354737694169/50000000000000 : ℝ), (10042950261447/100000000000000 : ℝ), (23623787169453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245382579/10000000000 : ℝ)|^4239 ≤ (21354737694169/50000000000000 : ℝ)^3215
        have hw : |(5245382579/10000000000 : ℝ)|=(5245382579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-874879203/5000000000 : ℝ)|^4239 ≤ (10042950261447/100000000000000 : ℝ)^3215
        have hw : |(-874879203/5000000000 : ℝ)|=(874879203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2831447357/5000000000 : ℝ)|^4239 ≤ (23623787169453/50000000000000 : ℝ)^3215
        have hw : |(2831447357/5000000000 : ℝ)|=(2831447357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s1_6 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524538249/1000000000 : ℝ)*x 0 + (2831447213/5000000000 : ℝ)*x 1 + (-34995179/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524538249/1000000000 : ℝ)^4239 ≤ (42709474432863/100000000000000 : ℝ)^3215 := by
    have hnat : (524538249 : ℕ)^4239*100000000000000^3215 ≤ 42709474432863^3215*1000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524538249 1000000000 42709474432863 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2831447213/5000000000 : ℝ)^4239 ≤ (47247571170681/100000000000000 : ℝ)^3215 := by
    have hnat : (2831447213 : ℕ)^4239*100000000000000^3215 ≤ 47247571170681^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831447213 5000000000 47247571170681 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34995179/200000000 : ℝ)^4239 ≤ (10042954378293/100000000000000 : ℝ)^3215 := by
    have hnat : (34995179 : ℕ)^4239*100000000000000^3215 ≤ 10042954378293^3215*200000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34995179 200000000 10042954378293 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524538249/1000000000 : ℝ), (2831447213/5000000000 : ℝ), (-34995179/200000000 : ℝ)] ![(42709474432863/100000000000000 : ℝ), (47247571170681/100000000000000 : ℝ), (10042954378293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524538249/1000000000 : ℝ)|^4239 ≤ (42709474432863/100000000000000 : ℝ)^3215
        have hw : |(524538249/1000000000 : ℝ)|=(524538249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2831447213/5000000000 : ℝ)|^4239 ≤ (47247571170681/100000000000000 : ℝ)^3215
        have hw : |(2831447213/5000000000 : ℝ)|=(2831447213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34995179/200000000 : ℝ)|^4239 ≤ (10042954378293/100000000000000 : ℝ)^3215
        have hw : |(-34995179/200000000 : ℝ)|=(34995179/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s1_7 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4304774503/10000000000 : ℝ)*x 0 + (4996100541/10000000000 : ℝ)*x 1 + (3707990319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304774503/10000000000 : ℝ)^4239 ≤ (32912513443447/100000000000000 : ℝ)^3215 := by
    have hnat : (4304774503 : ℕ)^4239*100000000000000^3215 ≤ 32912513443447^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304774503 10000000000 32912513443447 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4996100541/10000000000 : ℝ)^4239 ≤ (20026870622009/50000000000000 : ℝ)^3215 := by
    have hnat : (4996100541 : ℕ)^4239*50000000000000^3215 ≤ 20026870622009^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4996100541 10000000000 20026870622009 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3707990319/10000000000 : ℝ)^4239 ≤ (13516872647341/50000000000000 : ℝ)^3215 := by
    have hnat : (3707990319 : ℕ)^4239*50000000000000^3215 ≤ 13516872647341^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3707990319 10000000000 13516872647341 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304774503/10000000000 : ℝ), (4996100541/10000000000 : ℝ), (3707990319/10000000000 : ℝ)] ![(32912513443447/100000000000000 : ℝ), (20026870622009/50000000000000 : ℝ), (13516872647341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304774503/10000000000 : ℝ)|^4239 ≤ (32912513443447/100000000000000 : ℝ)^3215
        have hw : |(4304774503/10000000000 : ℝ)|=(4304774503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4996100541/10000000000 : ℝ)|^4239 ≤ (20026870622009/50000000000000 : ℝ)^3215
        have hw : |(4996100541/10000000000 : ℝ)|=(4996100541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3707990319/10000000000 : ℝ)|^4239 ≤ (13516872647341/50000000000000 : ℝ)^3215
        have hw : |(3707990319/10000000000 : ℝ)|=(3707990319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1279_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (931/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3139/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4989/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27331/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (931/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27331/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (931/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27331/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (931/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27331/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (931/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27331/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (931/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27331/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (931/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (931/100000 : ℝ) ^ (2119/512 : ℝ) ≤ (392779821081/100000000000000000000 : ℝ) := by
    have hpowers : (931/100000 : ℝ)^2119 ≤ (392779821081/100000000000000000000 : ℝ)^512 := by
      have hnat : (931 : ℕ)^2119*100000000000000000000^512 ≤ 392779821081^512*100000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        931 100000 392779821081 100000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (931/100000 : ℝ)) (X := (392779821081/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27331/100000 : ℝ) ^ (2119/512 : ℝ) ≤ (4661246321478347/1000000000000000000 : ℝ) := by
    have hpowers : (27331/100000 : ℝ)^2119 ≤ (4661246321478347/1000000000000000000 : ℝ)^512 := by
      have hnat : (27331 : ℕ)^2119*1000000000000000000^512 ≤ 4661246321478347^512*100000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27331 100000 4661246321478347 1000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27331/100000 : ℝ)) (X := (4661246321478347/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000392779821081/50000000000000000000 : ℝ) ≤ (62500000118631/62500000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50000000392779821081/50000000000000000000 : ℝ)^512 ≤ (62500000118631/62500000000000 : ℝ)^2119 := by
      have hnat : (50000000392779821081 : ℕ)^512*62500000000000^2119 ≤ 62500000118631^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000392779821081 50000000000000000000 62500000118631 62500000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62500000118631/62500000000000 : ℝ)) (X := (50000000392779821081/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100466125024927655781/100000000000000000000 : ℝ) ≤ (10011242819209041/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (100466125024927655781/100000000000000000000 : ℝ)^512 ≤ (10011242819209041/10000000000000000 : ℝ)^2119 := by
      have hnat : (100466125024927655781 : ℕ)^512*10000000000000000^2119 ≤ 10011242819209041^2119*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100466125024927655781 100000000000000000000 10011242819209041 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011242819209041/10000000000000000 : ℝ)) (X := (100466125024927655781/100000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (504661246321478347/500000000000000000 : ℝ) ≤ (5011242809718561/5000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (504661246321478347/500000000000000000 : ℝ)^512 ≤ (5011242809718561/5000000000000000 : ℝ)^2119 := by
      have hnat : (504661246321478347 : ℕ)^512*5000000000000000^2119 ≤ 5011242809718561^2119*500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        504661246321478347 500000000000000000 5011242809718561 5000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011242809718561/5000000000000000 : ℝ)) (X := (504661246321478347/500000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(392779821081/100000000000000000000 : ℝ) ≤ ((43996511067845442863/44000000000000000000 : ℝ)+2*(3747600076027/880000000000000 : ℝ)*(931/100000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (43996511067845442863/44000000000000000000 : ℝ)+2*(3747600076027/880000000000000 : ℝ)*(931/100000 : ℝ)=(62500000118631/62500000000000 : ℝ) by norm_num, show 1+2*(392779821081/100000000000000000000 : ℝ)=(50000000392779821081/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4661246321478347/1000000000000000000 : ℝ)+(392779821081/100000000000000000000 : ℝ) ≤ ((43996511067845442863/44000000000000000000 : ℝ)+(3747600076027/880000000000000 : ℝ)*((27331/100000 : ℝ)+(931/100000 : ℝ)))^(2119/512 : ℝ) := by
    rw [show (43996511067845442863/44000000000000000000 : ℝ)+(3747600076027/880000000000000 : ℝ)*((27331/100000 : ℝ)+(931/100000 : ℝ))=(10011242819209041/10000000000000000 : ℝ) by norm_num, show 1+(4661246321478347/1000000000000000000 : ℝ)+(392779821081/100000000000000000000 : ℝ)=(100466125024927655781/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4661246321478347/1000000000000000000 : ℝ) ≤ ((43996511067845442863/44000000000000000000 : ℝ)+2*(3747600076027/880000000000000 : ℝ)*(27331/100000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (43996511067845442863/44000000000000000000 : ℝ)+2*(3747600076027/880000000000000 : ℝ)*(27331/100000 : ℝ)=(5011242809718561/5000000000000000 : ℝ) by norm_num, show 1+2*(4661246321478347/1000000000000000000 : ℝ)=(504661246321478347/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43996511067845442863/44000000000000000000 : ℝ)*(X 1 0+X 2 0)+(3747600076027/880000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (931/100000 : ℝ)) (hi := (27331/100000 : ℝ)) (c := (43996511067845442863/44000000000000000000 : ℝ)) (alpha := (3747600076027/880000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43996511067845442863/44000000000000000000 : ℝ)*(X 0 1+X 2 1)+(3747600076027/880000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (931/100000 : ℝ)) (hi := (27331/100000 : ℝ)) (c := (43996511067845442863/44000000000000000000 : ℝ)) (alpha := (3747600076027/880000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43996511067845442863/44000000000000000000 : ℝ)*(X 0 2+X 1 2)+(3747600076027/880000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (931/100000 : ℝ)) (hi := (27331/100000 : ℝ)) (c := (43996511067845442863/44000000000000000000 : ℝ)) (alpha := (3747600076027/880000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2040914177/10000000000 : ℝ)*X 0 0+(708947091/1250000000 : ℝ)*X 0 1+(251225109/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1353092009/2500000000 : ℝ)*X 1 0+(-2388150773/10000000000 : ℝ)*X 1 1+(2512251011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5412367841/10000000000 : ℝ)*X 2 0+(1004900437/2000000000 : ℝ)*X 2 1+(-2388150819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2151706643/5000000000 : ℝ)*X 0 0+(369023487/1000000000 : ℝ)*X 0 1+(1253380867/2500000000 : ℝ)*X 0 2+(2151706643/5000000000 : ℝ)*X 1 0+(369023487/1000000000 : ℝ)*X 1 1+(1253380867/2500000000 : ℝ)*X 1 2+(2151706643/5000000000 : ℝ)*X 2 0+(369023487/1000000000 : ℝ)*X 2 1+(1253380867/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-255197499/1250000000 : ℝ)*X 0 0+(5033021883/10000000000 : ℝ)*X 0 1+(5662894323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5245382579/10000000000 : ℝ)*X 1 0+(-874879203/5000000000 : ℝ)*X 1 1+(2831447357/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((524538249/1000000000 : ℝ)*X 2 0+(2831447213/5000000000 : ℝ)*X 2 1+(-34995179/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4304774503/10000000000 : ℝ)*X 0 0+(4996100541/10000000000 : ℝ)*X 0 1+(3707990319/10000000000 : ℝ)*X 0 2+(4304774503/10000000000 : ℝ)*X 1 0+(4996100541/10000000000 : ℝ)*X 1 1+(3707990319/10000000000 : ℝ)*X 1 2+(4304774503/10000000000 : ℝ)*X 2 0+(4996100541/10000000000 : ℝ)*X 2 1+(3707990319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91448854035081815437261953/12500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80500513/100000000000000 : ℝ)*(base1) + (1521011567/100000000000000 : ℝ)*(base19) + (1465331833/100000000000000 : ℝ)*(base23) + (17525437/10000000000000 : ℝ)*(upper3) + (143715409/100000000000000 : ℝ)*(upper5) + (143820918605247/12500000000000 : ℝ)*(major0) + (143820918605247/12500000000000 : ℝ)*(major1) + (143820918605247/12500000000000 : ℝ)*(major2) + (96589082258099/6250000000000 : ℝ)*(sp0) + (48294743992217/3125000000000 : ℝ)*(sp1) + (772715931715339/50000000000000 : ℝ)*(sp2) + (755696952081109/100000000000000 : ℝ)*(sp3) + (8093133441/100000000000000 : ℝ)*(sp4) + (4092476201/100000000000000 : ℝ)*(sp7) + (755701125057823/100000000000000 : ℝ)*(f.failure) + (1545433328762511/100000000000000 : ℝ)*(f.sum) + (7794907289831/5500000000000000000000000000 : ℝ)*base66 + (1574929854626047839/550000000000000000000000000000000 : ℝ)*base68 + (1834643467026047839/550000000000000000000000000000000 : ℝ)*base70 + (164805278876047839/550000000000000000000000000000000 : ℝ)*base72 + (16087936110831/5500000000000000000000000000 : ℝ)*base74 + (2444901579776047839/550000000000000000000000000000000 : ℝ)*base76 + (283114603423952161/550000000000000000000000000000000 : ℝ)*base77 + (2107451335876047839/550000000000000000000000000000000 : ℝ)*base80 + (19391912555831/5500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (78478103/10000000000000000000000 : ℝ)*base90 + (78478103/10000000000000000000000 : ℝ)*base92 + (78478103/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1016547060041975938867440597/100000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62580307/100000000000000 : ℝ)*(base1) + (199323231/10000000000000 : ℝ)*(base19) + (1929879509/100000000000000 : ℝ)*(base23) + (16230651/6250000000000 : ℝ)*(upper3) + (45166859/20000000000000 : ℝ)*(upper5) + (590988500162401/50000000000000 : ℝ)*(major0) + (590988500162401/50000000000000 : ℝ)*(major1) + (590988500162401/50000000000000 : ℝ)*(major2) + (9890979361/100000000000000 : ℝ)*(sp1) + (1749420829/20000000000000 : ℝ)*(sp2) + (793811254224539/50000000000000 : ℝ)*(sp4) + (15876105616571/1000000000000 : ℝ)*(sp5) + (793805884442559/50000000000000 : ℝ)*(sp6) + (388165576675749/50000000000000 : ℝ)*(sp7) + (155266243186361/20000000000000 : ℝ)*(f.failure) + (1587622445868771/100000000000000 : ℝ)*(f.sum) + (829630157743/2000000000000000000000000000 : ℝ)*base66 + (1938048532372023267/200000000000000000000000000000000 : ℝ)*base68 + (2247628085172023267/200000000000000000000000000000000 : ℝ)*base70 + (1616945951972023267/200000000000000000000000000000000 : ℝ)*base72 + (3660777451743/2000000000000000000000000000 : ℝ)*base74 + (1894538714772023267/200000000000000000000000000000000 : ℝ)*base76 + (2643109725772023267/200000000000000000000000000000000 : ℝ)*base78 + (2331335576172023267/200000000000000000000000000000000 : ℝ)*base80 + (3818007935743/2000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4695679/2000000000000000000000 : ℝ)*base89 + (4695679/2000000000000000000000 : ℝ)*base91 + (4695679/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1279_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (931/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3139/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4989/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1279_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1279_s2_0 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086845699/10000000000 : ℝ)*x 0 + (1099662329/2000000000 : ℝ)*x 1 + (5168451643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086845699/10000000000 : ℝ)^4239 ≤ (12669026627281/100000000000000 : ℝ)^3215 := by
    have hnat : (2086845699 : ℕ)^4239*100000000000000^3215 ≤ 12669026627281^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086845699 10000000000 12669026627281 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099662329/2000000000 : ℝ)^4239 ≤ (9089093653247/20000000000000 : ℝ)^3215 := by
    have hnat : (1099662329 : ℕ)^4239*20000000000000^3215 ≤ 9089093653247^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099662329 2000000000 9089093653247 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5168451643/10000000000 : ℝ)^4239 ≤ (41885505091163/100000000000000 : ℝ)^3215 := by
    have hnat : (5168451643 : ℕ)^4239*100000000000000^3215 ≤ 41885505091163^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168451643 10000000000 41885505091163 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086845699/10000000000 : ℝ), (1099662329/2000000000 : ℝ), (5168451643/10000000000 : ℝ)] ![(12669026627281/100000000000000 : ℝ), (9089093653247/20000000000000 : ℝ), (41885505091163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086845699/10000000000 : ℝ)|^4239 ≤ (12669026627281/100000000000000 : ℝ)^3215
        have hw : |(-2086845699/10000000000 : ℝ)|=(2086845699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099662329/2000000000 : ℝ)|^4239 ≤ (9089093653247/20000000000000 : ℝ)^3215
        have hw : |(1099662329/2000000000 : ℝ)|=(1099662329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5168451643/10000000000 : ℝ)|^4239 ≤ (41885505091163/100000000000000 : ℝ)^3215
        have hw : |(5168451643/10000000000 : ℝ)|=(5168451643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s2_1 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671320819/1250000000 : ℝ)*x 0 + (-1128962733/5000000000 : ℝ)*x 1 + (5168452521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671320819/1250000000 : ℝ)^4239 ≤ (44058490745147/100000000000000 : ℝ)^3215 := by
    have hnat : (671320819 : ℕ)^4239*100000000000000^3215 ≤ 44058490745147^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671320819 1250000000 44058490745147 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128962733/5000000000 : ℝ)^4239 ≤ (14055994771161/100000000000000 : ℝ)^3215 := by
    have hnat : (1128962733 : ℕ)^4239*100000000000000^3215 ≤ 14055994771161^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128962733 5000000000 14055994771161 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5168452521/10000000000 : ℝ)^4239 ≤ (10471378618209/25000000000000 : ℝ)^3215 := by
    have hnat : (5168452521 : ℕ)^4239*25000000000000^3215 ≤ 10471378618209^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168452521 10000000000 10471378618209 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671320819/1250000000 : ℝ), (-1128962733/5000000000 : ℝ), (5168452521/10000000000 : ℝ)] ![(44058490745147/100000000000000 : ℝ), (14055994771161/100000000000000 : ℝ), (10471378618209/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671320819/1250000000 : ℝ)|^4239 ≤ (44058490745147/100000000000000 : ℝ)^3215
        have hw : |(671320819/1250000000 : ℝ)|=(671320819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1128962733/5000000000 : ℝ)|^4239 ≤ (14055994771161/100000000000000 : ℝ)^3215
        have hw : |(-1128962733/5000000000 : ℝ)|=(1128962733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5168452521/10000000000 : ℝ)|^4239 ≤ (10471378618209/25000000000000 : ℝ)^3215
        have hw : |(5168452521/10000000000 : ℝ)|=(5168452521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s2_2 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074113413/2000000000 : ℝ)*x 0 + (5168451799/10000000000 : ℝ)*x 1 + (-225792573/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074113413/2000000000 : ℝ)^4239 ≤ (22029248147039/50000000000000 : ℝ)^3215 := by
    have hnat : (1074113413 : ℕ)^4239*50000000000000^3215 ≤ 22029248147039^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074113413 2000000000 22029248147039 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5168451799/10000000000 : ℝ)^4239 ≤ (20942753379033/50000000000000 : ℝ)^3215 := by
    have hnat : (5168451799 : ℕ)^4239*50000000000000^3215 ≤ 20942753379033^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168451799 10000000000 20942753379033 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225792573/1000000000 : ℝ)^4239 ≤ (14055996938059/100000000000000 : ℝ)^3215 := by
    have hnat : (225792573 : ℕ)^4239*100000000000000^3215 ≤ 14055996938059^3215*1000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225792573 1000000000 14055996938059 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074113413/2000000000 : ℝ), (5168451799/10000000000 : ℝ), (-225792573/1000000000 : ℝ)] ![(22029248147039/50000000000000 : ℝ), (20942753379033/50000000000000 : ℝ), (14055996938059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074113413/2000000000 : ℝ)|^4239 ≤ (22029248147039/50000000000000 : ℝ)^3215
        have hw : |(1074113413/2000000000 : ℝ)|=(1074113413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5168451799/10000000000 : ℝ)|^4239 ≤ (20942753379033/50000000000000 : ℝ)^3215
        have hw : |(5168451799/10000000000 : ℝ)|=(5168451799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225792573/1000000000 : ℝ)|^4239 ≤ (14055996938059/100000000000000 : ℝ)^3215
        have hw : |(-225792573/1000000000 : ℝ)|=(225792573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s2_3 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135477811/312500000 : ℝ)*x 0 + (4010575603/10000000000 : ℝ)*x 1 + (4685155881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135477811/312500000 : ℝ)^4239 ≤ (16610239469911/50000000000000 : ℝ)^3215 := by
    have hnat : (135477811 : ℕ)^4239*50000000000000^3215 ≤ 16610239469911^3215*312500000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135477811 312500000 16610239469911 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010575603/10000000000 : ℝ)^4239 ≤ (29979560860821/100000000000000 : ℝ)^3215 := by
    have hnat : (4010575603 : ℕ)^4239*100000000000000^3215 ≤ 29979560860821^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010575603 10000000000 29979560860821 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4685155881/10000000000 : ℝ)^4239 ≤ (7359992038627/20000000000000 : ℝ)^3215 := by
    have hnat : (4685155881 : ℕ)^4239*20000000000000^3215 ≤ 7359992038627^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4685155881 10000000000 7359992038627 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135477811/312500000 : ℝ), (4010575603/10000000000 : ℝ), (4685155881/10000000000 : ℝ)] ![(16610239469911/50000000000000 : ℝ), (29979560860821/100000000000000 : ℝ), (7359992038627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135477811/312500000 : ℝ)|^4239 ≤ (16610239469911/50000000000000 : ℝ)^3215
        have hw : |(135477811/312500000 : ℝ)|=(135477811/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010575603/10000000000 : ℝ)|^4239 ≤ (29979560860821/100000000000000 : ℝ)^3215
        have hw : |(4010575603/10000000000 : ℝ)|=(4010575603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4685155881/10000000000 : ℝ)|^4239 ≤ (7359992038627/20000000000000 : ℝ)^3215
        have hw : |(4685155881/10000000000 : ℝ)|=(4685155881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s2_4 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-260866621/1250000000 : ℝ)*x 0 + (2585337711/5000000000 : ℝ)*x 1 + (5496066863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260866621/1250000000 : ℝ)^4239 ≤ (12669725178479/100000000000000 : ℝ)^3215 := by
    have hnat : (260866621 : ℕ)^4239*100000000000000^3215 ≤ 12669725178479^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260866621 1250000000 12669725178479 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585337711/5000000000 : ℝ)^4239 ≤ (20954634205621/50000000000000 : ℝ)^3215 := by
    have hnat : (2585337711 : ℕ)^4239*50000000000000^3215 ≤ 20954634205621^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585337711 5000000000 20954634205621 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496066863/10000000000 : ℝ)^4239 ≤ (45421006399227/100000000000000 : ℝ)^3215 := by
    have hnat : (5496066863 : ℕ)^4239*100000000000000^3215 ≤ 45421006399227^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496066863 10000000000 45421006399227 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-260866621/1250000000 : ℝ), (2585337711/5000000000 : ℝ), (5496066863/10000000000 : ℝ)] ![(12669725178479/100000000000000 : ℝ), (20954634205621/50000000000000 : ℝ), (45421006399227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-260866621/1250000000 : ℝ)|^4239 ≤ (12669725178479/100000000000000 : ℝ)^3215
        have hw : |(-260866621/1250000000 : ℝ)|=(260866621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2585337711/5000000000 : ℝ)|^4239 ≤ (20954634205621/50000000000000 : ℝ)^3215
        have hw : |(2585337711/5000000000 : ℝ)|=(2585337711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496066863/10000000000 : ℝ)|^4239 ≤ (45421006399227/100000000000000 : ℝ)^3215
        have hw : |(5496066863/10000000000 : ℝ)|=(5496066863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s2_5 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643076937/5000000000 : ℝ)*x 0 + (-1930310437/10000000000 : ℝ)*x 1 + (5496067023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643076937/5000000000 : ℝ)^4239 ≤ (43147723773551/100000000000000 : ℝ)^3215 := by
    have hnat : (2643076937 : ℕ)^4239*100000000000000^3215 ≤ 43147723773551^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643076937 5000000000 43147723773551 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1930310437/10000000000 : ℝ)^4239 ≤ (5715634036823/50000000000000 : ℝ)^3215 := by
    have hnat : (1930310437 : ℕ)^4239*50000000000000^3215 ≤ 5715634036823^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930310437 10000000000 5715634036823 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496067023/10000000000 : ℝ)^4239 ≤ (11355252035667/25000000000000 : ℝ)^3215 := by
    have hnat : (5496067023 : ℕ)^4239*25000000000000^3215 ≤ 11355252035667^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496067023 10000000000 11355252035667 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643076937/5000000000 : ℝ), (-1930310437/10000000000 : ℝ), (5496067023/10000000000 : ℝ)] ![(43147723773551/100000000000000 : ℝ), (5715634036823/50000000000000 : ℝ), (11355252035667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643076937/5000000000 : ℝ)|^4239 ≤ (43147723773551/100000000000000 : ℝ)^3215
        have hw : |(2643076937/5000000000 : ℝ)|=(2643076937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1930310437/10000000000 : ℝ)|^4239 ≤ (5715634036823/50000000000000 : ℝ)^3215
        have hw : |(-1930310437/10000000000 : ℝ)|=(1930310437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496067023/10000000000 : ℝ)|^4239 ≤ (11355252035667/25000000000000 : ℝ)^3215
        have hw : |(5496067023/10000000000 : ℝ)|=(5496067023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s2_6 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643077031/5000000000 : ℝ)*x 0 + (687008359/1250000000 : ℝ)*x 1 + (-482577597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643077031/5000000000 : ℝ)^4239 ≤ (43147725796843/100000000000000 : ℝ)^3215 := by
    have hnat : (2643077031 : ℕ)^4239*100000000000000^3215 ≤ 43147725796843^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643077031 5000000000 43147725796843 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687008359/1250000000 : ℝ)^4239 ≤ (2838812906081/6250000000000 : ℝ)^3215 := by
    have hnat : (687008359 : ℕ)^4239*6250000000000^3215 ≤ 2838812906081^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687008359 1250000000 2838812906081 6250000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482577597/2500000000 : ℝ)^4239 ≤ (2286253538209/20000000000000 : ℝ)^3215 := by
    have hnat : (482577597 : ℕ)^4239*20000000000000^3215 ≤ 2286253538209^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482577597 2500000000 2286253538209 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643077031/5000000000 : ℝ), (687008359/1250000000 : ℝ), (-482577597/2500000000 : ℝ)] ![(43147725796843/100000000000000 : ℝ), (2838812906081/6250000000000 : ℝ), (2286253538209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643077031/5000000000 : ℝ)|^4239 ≤ (43147725796843/100000000000000 : ℝ)^3215
        have hw : |(2643077031/5000000000 : ℝ)|=(2643077031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(687008359/1250000000 : ℝ)|^4239 ≤ (2838812906081/6250000000000 : ℝ)^3215
        have hw : |(687008359/1250000000 : ℝ)|=(687008359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-482577597/2500000000 : ℝ)|^4239 ≤ (2286253538209/20000000000000 : ℝ)^3215
        have hw : |(-482577597/2500000000 : ℝ)|=(482577597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s2_7 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4335468773/10000000000 : ℝ)*x 0 + (4680607289/10000000000 : ℝ)*x 1 + (803034041/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335468773/10000000000 : ℝ)^4239 ≤ (33222285662731/100000000000000 : ℝ)^3215 := by
    have hnat : (4335468773 : ℕ)^4239*100000000000000^3215 ≤ 33222285662731^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335468773 10000000000 33222285662731 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4680607289/10000000000 : ℝ)^4239 ≤ (4594107596637/12500000000000 : ℝ)^3215 := by
    have hnat : (4680607289 : ℕ)^4239*12500000000000^3215 ≤ 4594107596637^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4680607289 10000000000 4594107596637 12500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803034041/2000000000 : ℝ)^4239 ≤ (15012426774779/50000000000000 : ℝ)^3215 := by
    have hnat : (803034041 : ℕ)^4239*50000000000000^3215 ≤ 15012426774779^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803034041 2000000000 15012426774779 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335468773/10000000000 : ℝ), (4680607289/10000000000 : ℝ), (803034041/2000000000 : ℝ)] ![(33222285662731/100000000000000 : ℝ), (4594107596637/12500000000000 : ℝ), (15012426774779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335468773/10000000000 : ℝ)|^4239 ≤ (33222285662731/100000000000000 : ℝ)^3215
        have hw : |(4335468773/10000000000 : ℝ)|=(4335468773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4680607289/10000000000 : ℝ)|^4239 ≤ (4594107596637/12500000000000 : ℝ)^3215
        have hw : |(4680607289/10000000000 : ℝ)|=(4680607289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(803034041/2000000000 : ℝ)|^4239 ≤ (15012426774779/50000000000000 : ℝ)^3215
        have hw : |(803034041/2000000000 : ℝ)|=(803034041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1279_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4989/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3139/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (294/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8189/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4989/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3139/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4989/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3139/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4989/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3139/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4989/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3139/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4989/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3139/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4989/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3139/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3139/50000 : ℝ) ^ (2119/512 : ℝ) ≤ (1058222210829401/100000000000000000000 : ℝ) := by
    have hpowers : (3139/50000 : ℝ)^2119 ≤ (1058222210829401/100000000000000000000 : ℝ)^512 := by
      have hnat : (3139 : ℕ)^2119*100000000000000000000^512 ≤ 1058222210829401^512*50000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3139 50000 1058222210829401 100000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3139/50000 : ℝ)) (X := (1058222210829401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hpowhi : (4989/25000 : ℝ) ^ (2119/512 : ℝ) ≤ (7927091618424961/6250000000000000000 : ℝ) := by
    have hpowers : (4989/25000 : ℝ)^2119 ≤ (7927091618424961/6250000000000000000 : ℝ)^512 := by
      have hnat : (4989 : ℕ)^2119*6250000000000000000^512 ≤ 7927091618424961^512*25000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4989 25000 7927091618424961 6250000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4989/25000 : ℝ)) (X := (7927091618424961/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001058222210829401/50000000000000000000 : ℝ) ≤ (10000051137840851/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50001058222210829401/50000000000000000000 : ℝ)^512 ≤ (10000051137840851/10000000000000000 : ℝ)^2119 := by
      have hnat : (50001058222210829401 : ℕ)^512*10000000000000000^2119 ≤ 10000051137840851^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001058222210829401 50000000000000000000 10000051137840851 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000051137840851/10000000000000000 : ℝ)) (X := (50001058222210829401/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100127891688105628777/100000000000000000000 : ℝ) ≤ (5001544332545593/5000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (100127891688105628777/100000000000000000000 : ℝ)^512 ≤ (5001544332545593/5000000000000000 : ℝ)^2119 := by
      have hnat : (100127891688105628777 : ℕ)^512*5000000000000000^2119 ≤ 5001544332545593^2119*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100127891688105628777 100000000000000000000 5001544332545593 5000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001544332545593/5000000000000000 : ℝ)) (X := (100127891688105628777/100000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3132927091618424961/3125000000000000000 : ℝ) ≤ (10006126192341521/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (3132927091618424961/3125000000000000000 : ℝ)^512 ≤ (10006126192341521/10000000000000000 : ℝ)^2119 := by
      have hnat : (3132927091618424961 : ℕ)^512*10000000000000000^2119 ≤ 10006126192341521^2119*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3132927091618424961 3125000000000000000 10006126192341521 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006126192341521/10000000000000000 : ℝ)) (X := (3132927091618424961/3125000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1058222210829401/100000000000000000000 : ℝ) ≤ ((68371280135615976859/68390000000000000000 : ℝ)+2*(607505450067/273560000000000 : ℝ)*(3139/50000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (68371280135615976859/68390000000000000000 : ℝ)+2*(607505450067/273560000000000 : ℝ)*(3139/50000 : ℝ)=(10000051137840851/10000000000000000 : ℝ) by norm_num, show 1+2*(1058222210829401/100000000000000000000 : ℝ)=(50001058222210829401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7927091618424961/6250000000000000000 : ℝ)+(1058222210829401/100000000000000000000 : ℝ) ≤ ((68371280135615976859/68390000000000000000 : ℝ)+(607505450067/273560000000000 : ℝ)*((4989/25000 : ℝ)+(3139/50000 : ℝ)))^(2119/512 : ℝ) := by
    rw [show (68371280135615976859/68390000000000000000 : ℝ)+(607505450067/273560000000000 : ℝ)*((4989/25000 : ℝ)+(3139/50000 : ℝ))=(5001544332545593/5000000000000000 : ℝ) by norm_num, show 1+(7927091618424961/6250000000000000000 : ℝ)+(1058222210829401/100000000000000000000 : ℝ)=(100127891688105628777/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7927091618424961/6250000000000000000 : ℝ) ≤ ((68371280135615976859/68390000000000000000 : ℝ)+2*(607505450067/273560000000000 : ℝ)*(4989/25000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (68371280135615976859/68390000000000000000 : ℝ)+2*(607505450067/273560000000000 : ℝ)*(4989/25000 : ℝ)=(10006126192341521/10000000000000000 : ℝ) by norm_num, show 1+2*(7927091618424961/6250000000000000000 : ℝ)=(3132927091618424961/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68371280135615976859/68390000000000000000 : ℝ)*(X 1 0+X 2 0)+(607505450067/273560000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (3139/50000 : ℝ)) (hi := (4989/25000 : ℝ)) (c := (68371280135615976859/68390000000000000000 : ℝ)) (alpha := (607505450067/273560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68371280135615976859/68390000000000000000 : ℝ)*(X 0 1+X 2 1)+(607505450067/273560000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (3139/50000 : ℝ)) (hi := (4989/25000 : ℝ)) (c := (68371280135615976859/68390000000000000000 : ℝ)) (alpha := (607505450067/273560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68371280135615976859/68390000000000000000 : ℝ)*(X 0 2+X 1 2)+(607505450067/273560000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (3139/50000 : ℝ)) (hi := (4989/25000 : ℝ)) (c := (68371280135615976859/68390000000000000000 : ℝ)) (alpha := (607505450067/273560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2086845699/10000000000 : ℝ)*X 0 0+(1099662329/2000000000 : ℝ)*X 0 1+(5168451643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((671320819/1250000000 : ℝ)*X 1 0+(-1128962733/5000000000 : ℝ)*X 1 1+(5168452521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074113413/2000000000 : ℝ)*X 2 0+(5168451799/10000000000 : ℝ)*X 2 1+(-225792573/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135477811/312500000 : ℝ)*X 0 0+(4010575603/10000000000 : ℝ)*X 0 1+(4685155881/10000000000 : ℝ)*X 0 2+(135477811/312500000 : ℝ)*X 1 0+(4010575603/10000000000 : ℝ)*X 1 1+(4685155881/10000000000 : ℝ)*X 1 2+(135477811/312500000 : ℝ)*X 2 0+(4010575603/10000000000 : ℝ)*X 2 1+(4685155881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-260866621/1250000000 : ℝ)*X 0 0+(2585337711/5000000000 : ℝ)*X 0 1+(5496066863/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643076937/5000000000 : ℝ)*X 1 0+(-1930310437/10000000000 : ℝ)*X 1 1+(5496067023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643077031/5000000000 : ℝ)*X 2 0+(687008359/1250000000 : ℝ)*X 2 1+(-482577597/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4335468773/10000000000 : ℝ)*X 0 0+(4680607289/10000000000 : ℝ)*X 0 1+(803034041/2000000000 : ℝ)*X 0 2+(4335468773/10000000000 : ℝ)*X 1 0+(4680607289/10000000000 : ℝ)*X 1 1+(803034041/2000000000 : ℝ)*X 1 2+(4335468773/10000000000 : ℝ)*X 2 0+(4680607289/10000000000 : ℝ)*X 2 1+(803034041/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (272965711719287646673151421/341950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19842349/2000000000000 : ℝ)*(base19) + (625485723/50000000000000 : ℝ)*(base23) + (371658883/100000000000000 : ℝ)*(upper3) + (16502433/100000000000000 : ℝ)*(upper4) + (115799287/50000000000000 : ℝ)*(upper5) + (225702046833009/10000000000000 : ℝ)*(major0) + (225702046833009/10000000000000 : ℝ)*(major1) + (225702046833009/10000000000000 : ℝ)*(major2) + (151580089982807/5000000000000 : ℝ)*(sp0) + (378951527398553/12500000000000 : ℝ)*(sp1) + (757902990083607/25000000000000 : ℝ)*(sp2) + (148241450946477/10000000000000 : ℝ)*(sp3) + (11411649733/100000000000000 : ℝ)*(sp4) + (2637856157/20000000000000 : ℝ)*(sp7) + (741213849372777/50000000000000 : ℝ)*(f.failure) + (1515806605652937/50000000000000 : ℝ)*(f.sum) + (106032388281/106859375000000000000000000 : ℝ)*base66 + (563985666625455533/97700000000000000000000000000000 : ℝ)*base67 + (1270923512939355533/97700000000000000000000000000000 : ℝ)*base69 + (674596614937055533/97700000000000000000000000000000 : ℝ)*base71 + (24646132185917/3419500000000000000000000000 : ℝ)*base74 + (1146387149440855533/97700000000000000000000000000000 : ℝ)*base75 + (1369984203212655533/97700000000000000000000000000000 : ℝ)*base77 + (506877735721255533/97700000000000000000000000000000 : ℝ)*base79 + (1213015234933/683900000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (79768497/5000000000000000000000 : ℝ)*base90 + (79768497/5000000000000000000000 : ℝ)*base92 + (79768497/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10010528898649474850481620139/1709750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (272715003/25000000000000 : ℝ)*(base19) + (87319743/6250000000000 : ℝ)*(base23) + (184361973/100000000000000 : ℝ)*(upper3) + (14257337/20000000000000 : ℝ)*(lower4) + (67440779/100000000000000 : ℝ)*(upper5) + (1143997979870693/50000000000000 : ℝ)*(major0) + (1143997979870693/50000000000000 : ℝ)*(major1) + (1143997979870693/50000000000000 : ℝ)*(major2) + (2717565679/25000000000000 : ℝ)*(sp1) + (461226301/3125000000000 : ℝ)*(sp2) + (1536609547118221/50000000000000 : ℝ)*(sp4) + (1536603566556857/50000000000000 : ℝ)*(sp5) + (3073202937878921/100000000000000 : ℝ)*(sp6) + (751386315040387/50000000000000 : ℝ)*(sp7) + (751386315040387/50000000000000 : ℝ)*(f.failure) + (1536609547118221/50000000000000 : ℝ)*(f.sum) + (54066678986237/6839000000000000000000000000 : ℝ)*base65 + (697903203316149041/488500000000000000000000000000000 : ℝ)*base67 + (1896749845764850959/488500000000000000000000000000000 : ℝ)*base70 + (4381152481956149041/488500000000000000000000000000000 : ℝ)*base71 + (13808545987363/6839000000000000000000000000 : ℝ)*base73 + (1947426353126850959/488500000000000000000000000000000 : ℝ)*base76 + (395737974967149041/488500000000000000000000000000000 : ℝ)*base77 + (3660571409710149041/488500000000000000000000000000000 : ℝ)*base79 + (122250622313/6839000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (28055707/5000000000000000000000 : ℝ)*base90 + (28055707/5000000000000000000000 : ℝ)*base92 + (28055707/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1279_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4989/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3139/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (294/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1279_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1279_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (294/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1279_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1279_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1279_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (294/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1279_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
