-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1108_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:07.890567+00:00
-- url     : https://prove2.me/submissions/f2268a92-acb8-4e18-8e31-b0582d927138

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
theorem support_rectangle_w1108_s6_0 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-87328631/400000000 : ℝ)*x 0 + (5394065263/10000000000 : ℝ)*x 1 + (2632387627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87328631/400000000 : ℝ)^8301 ≤ (3315704085343/25000000000000 : ℝ)^6253 := by
    have hnat : (87328631 : ℕ)^8301*25000000000000^6253 ≤ 3315704085343^6253*400000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87328631 400000000 3315704085343 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394065263/10000000000 : ℝ)^8301 ≤ (44066914379683/100000000000000 : ℝ)^6253 := by
    have hnat : (5394065263 : ℕ)^8301*100000000000000^6253 ≤ 44066914379683^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394065263 10000000000 44066914379683 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632387627/5000000000 : ℝ)^8301 ≤ (42670269266573/100000000000000 : ℝ)^6253 := by
    have hnat : (2632387627 : ℕ)^8301*100000000000000^6253 ≤ 42670269266573^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632387627 5000000000 42670269266573 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87328631/400000000 : ℝ), (5394065263/10000000000 : ℝ), (2632387627/5000000000 : ℝ)] ![(3315704085343/25000000000000 : ℝ), (44066914379683/100000000000000 : ℝ), (42670269266573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87328631/400000000 : ℝ)|^8301 ≤ (3315704085343/25000000000000 : ℝ)^6253
        have hw : |(-87328631/400000000 : ℝ)|=(87328631/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394065263/10000000000 : ℝ)|^8301 ≤ (44066914379683/100000000000000 : ℝ)^6253
        have hw : |(5394065263/10000000000 : ℝ)|=(5394065263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632387627/5000000000 : ℝ)|^8301 ≤ (42670269266573/100000000000000 : ℝ)^6253
        have hw : |(2632387627/5000000000 : ℝ)|=(2632387627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s6_1 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336244579/2500000000 : ℝ)*x 0 + (-2248808717/10000000000 : ℝ)*x 1 + (2632387619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336244579/2500000000 : ℝ)^8301 ≤ (21767675269151/50000000000000 : ℝ)^6253 := by
    have hnat : (1336244579 : ℕ)^8301*50000000000000^6253 ≤ 21767675269151^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336244579 2500000000 21767675269151 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248808717/10000000000 : ℝ)^8301 ≤ (2758876070739/20000000000000 : ℝ)^6253 := by
    have hnat : (2248808717 : ℕ)^8301*20000000000000^6253 ≤ 2758876070739^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248808717 10000000000 2758876070739 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632387619/5000000000 : ℝ)^8301 ≤ (21335134547211/50000000000000 : ℝ)^6253 := by
    have hnat : (2632387619 : ℕ)^8301*50000000000000^6253 ≤ 21335134547211^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632387619 5000000000 21335134547211 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336244579/2500000000 : ℝ), (-2248808717/10000000000 : ℝ), (2632387619/5000000000 : ℝ)] ![(21767675269151/50000000000000 : ℝ), (2758876070739/20000000000000 : ℝ), (21335134547211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336244579/2500000000 : ℝ)|^8301 ≤ (21767675269151/50000000000000 : ℝ)^6253
        have hw : |(1336244579/2500000000 : ℝ)|=(1336244579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2248808717/10000000000 : ℝ)|^8301 ≤ (2758876070739/20000000000000 : ℝ)^6253
        have hw : |(-2248808717/10000000000 : ℝ)|=(2248808717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632387619/5000000000 : ℝ)|^8301 ≤ (21335134547211/50000000000000 : ℝ)^6253
        have hw : |(2632387619/5000000000 : ℝ)|=(2632387619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s6_2 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672489167/5000000000 : ℝ)*x 0 + (1316193809/2500000000 : ℝ)*x 1 + (-449761739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672489167/5000000000 : ℝ)^8301 ≤ (10883837683233/25000000000000 : ℝ)^6253 := by
    have hnat : (2672489167 : ℕ)^8301*25000000000000^6253 ≤ 10883837683233^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672489167 5000000000 10883837683233 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316193809/2500000000 : ℝ)^8301 ≤ (5333783634113/12500000000000 : ℝ)^6253 := by
    have hnat : (1316193809 : ℕ)^8301*12500000000000^6253 ≤ 5333783634113^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316193809 2500000000 5333783634113 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449761739/2000000000 : ℝ)^8301 ≤ (6897190087273/50000000000000 : ℝ)^6253 := by
    have hnat : (449761739 : ℕ)^8301*50000000000000^6253 ≤ 6897190087273^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449761739 2000000000 6897190087273 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672489167/5000000000 : ℝ), (1316193809/2500000000 : ℝ), (-449761739/2000000000 : ℝ)] ![(10883837683233/25000000000000 : ℝ), (5333783634113/12500000000000 : ℝ), (6897190087273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672489167/5000000000 : ℝ)|^8301 ≤ (10883837683233/25000000000000 : ℝ)^6253
        have hw : |(2672489167/5000000000 : ℝ)|=(2672489167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316193809/2500000000 : ℝ)|^8301 ≤ (5333783634113/12500000000000 : ℝ)^6253
        have hw : |(1316193809/2500000000 : ℝ)|=(1316193809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449761739/2000000000 : ℝ)|^8301 ≤ (6897190087273/50000000000000 : ℝ)^6253
        have hw : |(-449761739/2000000000 : ℝ)|=(449761739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s6_3 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369464137/10000000000 : ℝ)*x 0 + (4243584923/10000000000 : ℝ)*x 1 + (4499089879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369464137/10000000000 : ℝ)^8301 ≤ (8329141155343/25000000000000 : ℝ)^6253 := by
    have hnat : (4369464137 : ℕ)^8301*25000000000000^6253 ≤ 8329141155343^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369464137 10000000000 8329141155343 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243584923/10000000000 : ℝ)^8301 ≤ (16024221609367/50000000000000 : ℝ)^6253 := by
    have hnat : (4243584923 : ℕ)^8301*50000000000000^6253 ≤ 16024221609367^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243584923 10000000000 16024221609367 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499089879/10000000000 : ℝ)^8301 ≤ (17317496070399/50000000000000 : ℝ)^6253 := by
    have hnat : (4499089879 : ℕ)^8301*50000000000000^6253 ≤ 17317496070399^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499089879 10000000000 17317496070399 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369464137/10000000000 : ℝ), (4243584923/10000000000 : ℝ), (4499089879/10000000000 : ℝ)] ![(8329141155343/25000000000000 : ℝ), (16024221609367/50000000000000 : ℝ), (17317496070399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369464137/10000000000 : ℝ)|^8301 ≤ (8329141155343/25000000000000 : ℝ)^6253
        have hw : |(4369464137/10000000000 : ℝ)|=(4369464137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243584923/10000000000 : ℝ)|^8301 ≤ (16024221609367/50000000000000 : ℝ)^6253
        have hw : |(4243584923/10000000000 : ℝ)|=(4243584923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499089879/10000000000 : ℝ)|^8301 ≤ (17317496070399/50000000000000 : ℝ)^6253
        have hw : |(4499089879/10000000000 : ℝ)|=(4499089879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s6_4 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183220859/10000000000 : ℝ)*x 0 + (5265101711/10000000000 : ℝ)*x 1 + (5393737603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183220859/10000000000 : ℝ)^8301 ≤ (13262857341649/100000000000000 : ℝ)^6253 := by
    have hnat : (2183220859 : ℕ)^8301*100000000000000^6253 ≤ 13262857341649^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183220859 10000000000 13262857341649 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265101711/10000000000 : ℝ)^8301 ≤ (42673781779469/100000000000000 : ℝ)^6253 := by
    have hnat : (5265101711 : ℕ)^8301*100000000000000^6253 ≤ 42673781779469^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265101711 10000000000 42673781779469 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393737603/10000000000 : ℝ)^8301 ≤ (1762534434789/4000000000000 : ℝ)^6253 := by
    have hnat : (5393737603 : ℕ)^8301*4000000000000^6253 ≤ 1762534434789^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393737603 10000000000 1762534434789 4000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183220859/10000000000 : ℝ), (5265101711/10000000000 : ℝ), (5393737603/10000000000 : ℝ)] ![(13262857341649/100000000000000 : ℝ), (42673781779469/100000000000000 : ℝ), (1762534434789/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183220859/10000000000 : ℝ)|^8301 ≤ (13262857341649/100000000000000 : ℝ)^6253
        have hw : |(-2183220859/10000000000 : ℝ)|=(2183220859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265101711/10000000000 : ℝ)|^8301 ≤ (42673781779469/100000000000000 : ℝ)^6253
        have hw : |(5265101711/10000000000 : ℝ)|=(5265101711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393737603/10000000000 : ℝ)|^8301 ≤ (1762534434789/4000000000000 : ℝ)^6253
        have hw : |(5393737603/10000000000 : ℝ)|=(5393737603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s6_5 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166009561/312500000 : ℝ)*x 0 + (-1059923169/5000000000 : ℝ)*x 1 + (674217197/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166009561/312500000 : ℝ)^8301 ≤ (43182425000121/100000000000000 : ℝ)^6253 := by
    have hnat : (166009561 : ℕ)^8301*100000000000000^6253 ≤ 43182425000121^6253*312500000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166009561 312500000 43182425000121 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059923169/5000000000 : ℝ)^8301 ≤ (1594276799717/12500000000000 : ℝ)^6253 := by
    have hnat : (1059923169 : ℕ)^8301*12500000000000^6253 ≤ 1594276799717^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059923169 5000000000 1594276799717 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674217197/1250000000 : ℝ)^8301 ≤ (44063360576909/100000000000000 : ℝ)^6253 := by
    have hnat : (674217197 : ℕ)^8301*100000000000000^6253 ≤ 44063360576909^6253*1250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674217197 1250000000 44063360576909 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166009561/312500000 : ℝ), (-1059923169/5000000000 : ℝ), (674217197/1250000000 : ℝ)] ![(43182425000121/100000000000000 : ℝ), (1594276799717/12500000000000 : ℝ), (44063360576909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166009561/312500000 : ℝ)|^8301 ≤ (43182425000121/100000000000000 : ℝ)^6253
        have hw : |(166009561/312500000 : ℝ)|=(166009561/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1059923169/5000000000 : ℝ)|^8301 ≤ (1594276799717/12500000000000 : ℝ)^6253
        have hw : |(-1059923169/5000000000 : ℝ)|=(1059923169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674217197/1250000000 : ℝ)|^8301 ≤ (44063360576909/100000000000000 : ℝ)^6253
        have hw : |(674217197/1250000000 : ℝ)|=(674217197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s6_6 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328076491/2500000000 : ℝ)*x 0 + (5393737551/10000000000 : ℝ)*x 1 + (-2119846357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328076491/2500000000 : ℝ)^8301 ≤ (21591212564807/50000000000000 : ℝ)^6253 := by
    have hnat : (1328076491 : ℕ)^8301*50000000000000^6253 ≤ 21591212564807^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328076491 2500000000 21591212564807 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393737551/10000000000 : ℝ)^8301 ≤ (5507920038223/12500000000000 : ℝ)^6253 := by
    have hnat : (5393737551 : ℕ)^8301*12500000000000^6253 ≤ 5507920038223^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393737551 10000000000 5507920038223 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119846357/10000000000 : ℝ)^8301 ≤ (12754214549491/100000000000000 : ℝ)^6253 := by
    have hnat : (2119846357 : ℕ)^8301*100000000000000^6253 ≤ 12754214549491^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119846357 10000000000 12754214549491 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328076491/2500000000 : ℝ), (5393737551/10000000000 : ℝ), (-2119846357/10000000000 : ℝ)] ![(21591212564807/50000000000000 : ℝ), (5507920038223/12500000000000 : ℝ), (12754214549491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328076491/2500000000 : ℝ)|^8301 ≤ (21591212564807/50000000000000 : ℝ)^6253
        have hw : |(1328076491/2500000000 : ℝ)|=(1328076491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393737551/10000000000 : ℝ)|^8301 ≤ (5507920038223/12500000000000 : ℝ)^6253
        have hw : |(5393737551/10000000000 : ℝ)|=(5393737551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2119846357/10000000000 : ℝ)|^8301 ≤ (12754214549491/100000000000000 : ℝ)^6253
        have hw : |(-2119846357/10000000000 : ℝ)|=(2119846357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s6_7 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369474123/10000000000 : ℝ)*x 0 + (4498444631/10000000000 : ℝ)*x 1 + (2122116267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369474123/10000000000 : ℝ)^8301 ≤ (3331666570149/10000000000000 : ℝ)^6253 := by
    have hnat : (4369474123 : ℕ)^8301*10000000000000^6253 ≤ 3331666570149^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369474123 10000000000 3331666570149 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498444631/10000000000 : ℝ)^8301 ≤ (34628398141811/100000000000000 : ℝ)^6253 := by
    have hnat : (4498444631 : ℕ)^8301*100000000000000^6253 ≤ 34628398141811^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498444631 10000000000 34628398141811 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122116267/5000000000 : ℝ)^8301 ≤ (16027468077169/50000000000000 : ℝ)^6253 := by
    have hnat : (2122116267 : ℕ)^8301*50000000000000^6253 ≤ 16027468077169^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122116267 5000000000 16027468077169 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369474123/10000000000 : ℝ), (4498444631/10000000000 : ℝ), (2122116267/5000000000 : ℝ)] ![(3331666570149/10000000000000 : ℝ), (34628398141811/100000000000000 : ℝ), (16027468077169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369474123/10000000000 : ℝ)|^8301 ≤ (3331666570149/10000000000000 : ℝ)^6253
        have hw : |(4369474123/10000000000 : ℝ)|=(4369474123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498444631/10000000000 : ℝ)|^8301 ≤ (34628398141811/100000000000000 : ℝ)^6253
        have hw : |(4498444631/10000000000 : ℝ)|=(4498444631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122116267/5000000000 : ℝ)|^8301 ≤ (16027468077169/50000000000000 : ℝ)^6253
        have hw : |(2122116267/5000000000 : ℝ)|=(2122116267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1108_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (113/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7019/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (352/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (352/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (352/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (352/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (352/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (352/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (352/3125 : ℝ) ^ (2075/512 : ℝ) ≤ (2869407089643233/20000000000000000000 : ℝ) := by
    have hpowers : (352/3125 : ℝ)^2075 ≤ (2869407089643233/20000000000000000000 : ℝ)^512 := by
      have hnat : (352 : ℕ)^2075*20000000000000000000^512 ≤ 2869407089643233^512*3125^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        352 3125 2869407089643233 20000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (352/3125 : ℝ)) (X := (2869407089643233/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hpowhi : (563/4000 : ℝ) ^ (2075/512 : ℝ) ≤ (3539057125809703/10000000000000000000 : ℝ) := by
    have hpowers : (563/4000 : ℝ)^2075 ≤ (3539057125809703/10000000000000000000 : ℝ)^512 := by
      have hnat : (563 : ℕ)^2075*10000000000000000000^512 ≤ 3539057125809703^512*4000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 4000 3539057125809703 10000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/4000 : ℝ)) (X := (3539057125809703/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002869407089643233/10000000000000000000 : ℝ) ≤ (10000707941054319/10000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (10002869407089643233/10000000000000000000 : ℝ)^512 ≤ (10000707941054319/10000000000000000 : ℝ)^2075 := by
      have hnat : (10002869407089643233 : ℕ)^512*10000000000000000^2075 ≤ 10000707941054319^2075*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002869407089643233 10000000000000000000 10000707941054319 10000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000707941054319/10000000000000000 : ℝ)) (X := (10002869407089643233/10000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009947521341262639/20000000000000000000 : ℝ) ≤ (2000245406126899/2000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (20009947521341262639/20000000000000000000 : ℝ)^512 ≤ (2000245406126899/2000000000000000 : ℝ)^2075 := by
      have hnat : (20009947521341262639 : ℕ)^512*2000000000000000^2075 ≤ 2000245406126899^2075*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009947521341262639 20000000000000000000 2000245406126899 2000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000245406126899/2000000000000000 : ℝ)) (X := (20009947521341262639/20000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003539057125809703/5000000000000000000 : ℝ) ≤ (10001746120214671/10000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (5003539057125809703/5000000000000000000 : ℝ)^512 ≤ (10001746120214671/10000000000000000 : ℝ)^2075 := by
      have hnat : (5003539057125809703 : ℕ)^512*10000000000000000^2075 ≤ 10001746120214671^2075*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003539057125809703 5000000000000000000 10001746120214671 10000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001746120214671/10000000000000000 : ℝ)) (X := (5003539057125809703/5000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2869407089643233/20000000000000000000 : ℝ) ≤ ((28100295972241485781/28110000000000000000 : ℝ)+2*(32443098761/17568750000000 : ℝ)*(352/3125 : ℝ))^(2075/512 : ℝ) := by
    rw [show (28100295972241485781/28110000000000000000 : ℝ)+2*(32443098761/17568750000000 : ℝ)*(352/3125 : ℝ)=(10000707941054319/10000000000000000 : ℝ) by norm_num, show 1+2*(2869407089643233/20000000000000000000 : ℝ)=(10002869407089643233/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3539057125809703/10000000000000000000 : ℝ)+(2869407089643233/20000000000000000000 : ℝ) ≤ ((28100295972241485781/28110000000000000000 : ℝ)+(32443098761/17568750000000 : ℝ)*((563/4000 : ℝ)+(352/3125 : ℝ)))^(2075/512 : ℝ) := by
    rw [show (28100295972241485781/28110000000000000000 : ℝ)+(32443098761/17568750000000 : ℝ)*((563/4000 : ℝ)+(352/3125 : ℝ))=(2000245406126899/2000000000000000 : ℝ) by norm_num, show 1+(3539057125809703/10000000000000000000 : ℝ)+(2869407089643233/20000000000000000000 : ℝ)=(20009947521341262639/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3539057125809703/10000000000000000000 : ℝ) ≤ ((28100295972241485781/28110000000000000000 : ℝ)+2*(32443098761/17568750000000 : ℝ)*(563/4000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (28100295972241485781/28110000000000000000 : ℝ)+2*(32443098761/17568750000000 : ℝ)*(563/4000 : ℝ)=(10001746120214671/10000000000000000 : ℝ) by norm_num, show 1+2*(3539057125809703/10000000000000000000 : ℝ)=(5003539057125809703/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28100295972241485781/28110000000000000000 : ℝ)*(X 1 0+X 2 0)+(32443098761/17568750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (563/4000 : ℝ)) (c := (28100295972241485781/28110000000000000000 : ℝ)) (alpha := (32443098761/17568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28100295972241485781/28110000000000000000 : ℝ)*(X 0 1+X 2 1)+(32443098761/17568750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (563/4000 : ℝ)) (c := (28100295972241485781/28110000000000000000 : ℝ)) (alpha := (32443098761/17568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28100295972241485781/28110000000000000000 : ℝ)*(X 0 2+X 1 2)+(32443098761/17568750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (563/4000 : ℝ)) (c := (28100295972241485781/28110000000000000000 : ℝ)) (alpha := (32443098761/17568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87328631/400000000 : ℝ)*X 0 0+(5394065263/10000000000 : ℝ)*X 0 1+(2632387627/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336244579/2500000000 : ℝ)*X 1 0+(-2248808717/10000000000 : ℝ)*X 1 1+(2632387619/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672489167/5000000000 : ℝ)*X 2 0+(1316193809/2500000000 : ℝ)*X 2 1+(-449761739/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369464137/10000000000 : ℝ)*X 0 0+(4243584923/10000000000 : ℝ)*X 0 1+(4499089879/10000000000 : ℝ)*X 0 2+(4369464137/10000000000 : ℝ)*X 1 0+(4243584923/10000000000 : ℝ)*X 1 1+(4499089879/10000000000 : ℝ)*X 1 2+(4369464137/10000000000 : ℝ)*X 2 0+(4243584923/10000000000 : ℝ)*X 2 1+(4499089879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2183220859/10000000000 : ℝ)*X 0 0+(5265101711/10000000000 : ℝ)*X 0 1+(5393737603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((166009561/312500000 : ℝ)*X 1 0+(-1059923169/5000000000 : ℝ)*X 1 1+(674217197/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328076491/2500000000 : ℝ)*X 2 0+(5393737551/10000000000 : ℝ)*X 2 1+(-2119846357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369474123/10000000000 : ℝ)*X 0 0+(4498444631/10000000000 : ℝ)*X 0 1+(2122116267/5000000000 : ℝ)*X 0 2+(4369474123/10000000000 : ℝ)*X 1 0+(4498444631/10000000000 : ℝ)*X 1 1+(2122116267/5000000000 : ℝ)*X 1 2+(4369474123/10000000000 : ℝ)*X 2 0+(4498444631/10000000000 : ℝ)*X 2 1+(2122116267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1352344380043484084529/585625000000000000000000000 : ℝ) := by norm_num
    linear_combination (106936327/20000000000000 : ℝ)*(base19) + (260625717/50000000000000 : ℝ)*(base23) + (21100651/100000000000000 : ℝ)*(lower2) + (103907/200000000000 : ℝ)*(upper3) + (61806553/100000000000000 : ℝ)*(upper5) + (5824205629404861/100000000000000 : ℝ)*(major0) + (5824205629404861/100000000000000 : ℝ)*(major1) + (5824205629404861/100000000000000 : ℝ)*(major2) + (7734562893982563/100000000000000 : ℝ)*(sp0) + (7734577003493399/100000000000000 : ℝ)*(sp1) + (19336442542309/250000000000 : ℝ)*(sp2) + (1956912962490009/50000000000000 : ℝ)*(sp3) + (14644192471/100000000000000 : ℝ)*(sp4) + (7718680243/100000000000000 : ℝ)*(sp7) + (195691682183013/5000000000000 : ℝ)*(f.failure) + (3867288769087517/50000000000000 : ℝ)*(f.sum) + (7794560142427/4685000000000000000000000000 : ℝ)*base65 + (909238981170127147/937000000000000000000000000000000 : ℝ)*base67 + (1228269501603872853/937000000000000000000000000000000 : ℝ)*base70 + (12726138076316127147/937000000000000000000000000000000 : ℝ)*base71 + (173833586573/73203125000000000000000000 : ℝ)*base73 + (17119387478942872853/937000000000000000000000000000000 : ℝ)*base76 + (3891027978224127147/937000000000000000000000000000000 : ℝ)*base77 + (1060843481879872853/937000000000000000000000000000000 : ℝ)*base80 + (214320279023/73203125000000000000000000 : ℝ)*base81 + (802893/500000000000000000000 : ℝ)*base89 + (802893/500000000000000000000 : ℝ)*base91 + (802893/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43024484433074049771913761/9370000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (269436467/25000000000000 : ℝ)*(base19) + (1110021103/100000000000000 : ℝ)*(base23) + (89016609/100000000000000 : ℝ)*(upper3) + (13706429/100000000000000 : ℝ)*(lower4) + (126785973/100000000000000 : ℝ)*(upper5) + (234152079065581/4000000000000 : ℝ)*(major0) + (234152079065581/4000000000000 : ℝ)*(major1) + (234152079065581/4000000000000 : ℝ)*(major2) + (7491178137/25000000000000 : ℝ)*(sp1) + (28162115381/100000000000000 : ℝ)*(sp2) + (777388157657157/10000000000000 : ℝ)*(sp4) + (3886925267056577/50000000000000 : ℝ)*(sp5) + (7773852304435087/100000000000000 : ℝ)*(sp6) + (983430555912473/25000000000000 : ℝ)*(sp7) + (983430555912473/25000000000000 : ℝ)*(f.failure) + (777388157657157/10000000000000 : ℝ)*(f.sum) + (3035423228233/1405500000000000000000000000 : ℝ)*base66 + (446745817918025413/37480000000000000000000000000000 : ℝ)*base68 + (820243272329705413/37480000000000000000000000000000 : ℝ)*base70 + (129288732585625413/37480000000000000000000000000000 : ℝ)*base72 + (1229269842911/702750000000000000000000000 : ℝ)*base74 + (1349993628716345413/37480000000000000000000000000000 : ℝ)*base76 + (16684160686294587/37480000000000000000000000000000 : ℝ)*base77 + (939098111768865413/37480000000000000000000000000000 : ℝ)*base80 + (1588677970567/1405500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (31521953/2500000000000000000000 : ℝ)*base89 + (31521953/2500000000000000000000 : ℝ)*base91 + (31521953/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1108_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1108_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1108_s7_0 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-436649361/2000000000 : ℝ)*x 0 + (5393683379/10000000000 : ℝ)*x 1 + (5265136917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436649361/2000000000 : ℝ)^8301 ≤ (3315766646371/25000000000000 : ℝ)^6253 := by
    have hnat : (436649361 : ℕ)^8301*25000000000000^6253 ≤ 3315766646371^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436649361 2000000000 3315766646371 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393683379/10000000000 : ℝ)^8301 ≤ (44062772811097/100000000000000 : ℝ)^6253 := by
    have hnat : (5393683379 : ℕ)^8301*100000000000000^6253 ≤ 44062772811097^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393683379 10000000000 44062772811097 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265136917/10000000000 : ℝ)^8301 ≤ (21337080291279/50000000000000 : ℝ)^6253 := by
    have hnat : (5265136917 : ℕ)^8301*50000000000000^6253 ≤ 21337080291279^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265136917 10000000000 21337080291279 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436649361/2000000000 : ℝ), (5393683379/10000000000 : ℝ), (5265136917/10000000000 : ℝ)] ![(3315766646371/25000000000000 : ℝ), (44062772811097/100000000000000 : ℝ), (21337080291279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436649361/2000000000 : ℝ)|^8301 ≤ (3315766646371/25000000000000 : ℝ)^6253
        have hw : |(-436649361/2000000000 : ℝ)|=(436649361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393683379/10000000000 : ℝ)|^8301 ≤ (44062772811097/100000000000000 : ℝ)^6253
        have hw : |(5393683379/10000000000 : ℝ)|=(5393683379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265136917/10000000000 : ℝ)|^8301 ≤ (21337080291279/50000000000000 : ℝ)^6253
        have hw : |(5265136917/10000000000 : ℝ)|=(5265136917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s7_1 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068976643/2000000000 : ℝ)*x 0 + (-449691421/2000000000 : ℝ)*x 1 + (2632568457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068976643/2000000000 : ℝ)^8301 ≤ (43534322233411/100000000000000 : ℝ)^6253 := by
    have hnat : (1068976643 : ℕ)^8301*100000000000000^6253 ≤ 43534322233411^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068976643 2000000000 43534322233411 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449691421/2000000000 : ℝ)^8301 ≤ (6895758601411/50000000000000 : ℝ)^6253 := by
    have hnat : (449691421 : ℕ)^8301*50000000000000^6253 ≤ 6895758601411^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449691421 2000000000 6895758601411 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632568457/5000000000 : ℝ)^8301 ≤ (42674160550279/100000000000000 : ℝ)^6253 := by
    have hnat : (2632568457 : ℕ)^8301*100000000000000^6253 ≤ 42674160550279^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632568457 5000000000 42674160550279 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068976643/2000000000 : ℝ), (-449691421/2000000000 : ℝ), (2632568457/5000000000 : ℝ)] ![(43534322233411/100000000000000 : ℝ), (6895758601411/50000000000000 : ℝ), (42674160550279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068976643/2000000000 : ℝ)|^8301 ≤ (43534322233411/100000000000000 : ℝ)^6253
        have hw : |(1068976643/2000000000 : ℝ)|=(1068976643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-449691421/2000000000 : ℝ)|^8301 ≤ (6895758601411/50000000000000 : ℝ)^6253
        have hw : |(-449691421/2000000000 : ℝ)|=(449691421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632568457/5000000000 : ℝ)|^8301 ≤ (42674160550279/100000000000000 : ℝ)^6253
        have hw : |(2632568457/5000000000 : ℝ)|=(2632568457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s7_2 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672441607/5000000000 : ℝ)*x 0 + (2632568457/5000000000 : ℝ)*x 1 + (-2248457107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672441607/5000000000 : ℝ)^8301 ≤ (21767161111299/50000000000000 : ℝ)^6253 := by
    have hnat : (2672441607 : ℕ)^8301*50000000000000^6253 ≤ 21767161111299^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672441607 5000000000 21767161111299 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632568457/5000000000 : ℝ)^8301 ≤ (42674160550279/100000000000000 : ℝ)^6253 := by
    have hnat : (2632568457 : ℕ)^8301*100000000000000^6253 ≤ 42674160550279^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632568457 5000000000 42674160550279 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248457107/10000000000 : ℝ)^8301 ≤ (3447879304777/25000000000000 : ℝ)^6253 := by
    have hnat : (2248457107 : ℕ)^8301*25000000000000^6253 ≤ 3447879304777^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248457107 10000000000 3447879304777 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672441607/5000000000 : ℝ), (2632568457/5000000000 : ℝ), (-2248457107/10000000000 : ℝ)] ![(21767161111299/50000000000000 : ℝ), (42674160550279/100000000000000 : ℝ), (3447879304777/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672441607/5000000000 : ℝ)|^8301 ≤ (21767161111299/50000000000000 : ℝ)^6253
        have hw : |(2672441607/5000000000 : ℝ)|=(2672441607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632568457/5000000000 : ℝ)|^8301 ≤ (42674160550279/100000000000000 : ℝ)^6253
        have hw : |(2632568457/5000000000 : ℝ)|=(2632568457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2248457107/10000000000 : ℝ)|^8301 ≤ (3447879304777/25000000000000 : ℝ)^6253
        have hw : |(-2248457107/10000000000 : ℝ)|=(2248457107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s7_3 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873896619/2000000000 : ℝ)*x 0 + (424431719/1000000000 : ℝ)*x 1 + (1124588171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873896619/2000000000 : ℝ)^8301 ≤ (1665837825889/5000000000000 : ℝ)^6253 := by
    have hnat : (873896619 : ℕ)^8301*5000000000000^6253 ≤ 1665837825889^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873896619 2000000000 1665837825889 5000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424431719/1000000000 : ℝ)^8301 ≤ (3205578493777/10000000000000 : ℝ)^6253 := by
    have hnat : (424431719 : ℕ)^8301*10000000000000^6253 ≤ 3205578493777^6253*1000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424431719 1000000000 3205578493777 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124588171/2500000000 : ℝ)^8301 ≤ (8656864632689/25000000000000 : ℝ)^6253 := by
    have hnat : (1124588171 : ℕ)^8301*25000000000000^6253 ≤ 8656864632689^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124588171 2500000000 8656864632689 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873896619/2000000000 : ℝ), (424431719/1000000000 : ℝ), (1124588171/2500000000 : ℝ)] ![(1665837825889/5000000000000 : ℝ), (3205578493777/10000000000000 : ℝ), (8656864632689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873896619/2000000000 : ℝ)|^8301 ≤ (1665837825889/5000000000000 : ℝ)^6253
        have hw : |(873896619/2000000000 : ℝ)|=(873896619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424431719/1000000000 : ℝ)|^8301 ≤ (3205578493777/10000000000000 : ℝ)^6253
        have hw : |(424431719/1000000000 : ℝ)|=(424431719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124588171/2500000000 : ℝ)|^8301 ≤ (8656864632689/25000000000000 : ℝ)^6253
        have hw : |(1124588171/2500000000 : ℝ)|=(1124588171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s7_4 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-436650359/2000000000 : ℝ)*x 0 + (5265459629/10000000000 : ℝ)*x 1 + (539335949/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436650359/2000000000 : ℝ)^8301 ≤ (6631553413939/50000000000000 : ℝ)^6253 := by
    have hnat : (436650359 : ℕ)^8301*50000000000000^6253 ≤ 6631553413939^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436650359 2000000000 6631553413939 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265459629/10000000000 : ℝ)^8301 ≤ (42677632878853/100000000000000 : ℝ)^6253 := by
    have hnat : (5265459629 : ℕ)^8301*100000000000000^6253 ≤ 42677632878853^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265459629 10000000000 42677632878853 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539335949/1000000000 : ℝ)^8301 ≤ (22029630139557/50000000000000 : ℝ)^6253 := by
    have hnat : (539335949 : ℕ)^8301*50000000000000^6253 ≤ 22029630139557^6253*1000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539335949 1000000000 22029630139557 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436650359/2000000000 : ℝ), (5265459629/10000000000 : ℝ), (539335949/1000000000 : ℝ)] ![(6631553413939/50000000000000 : ℝ), (42677632878853/100000000000000 : ℝ), (22029630139557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436650359/2000000000 : ℝ)|^8301 ≤ (6631553413939/50000000000000 : ℝ)^6253
        have hw : |(-436650359/2000000000 : ℝ)|=(436650359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265459629/10000000000 : ℝ)|^8301 ≤ (42677632878853/100000000000000 : ℝ)^6253
        have hw : |(5265459629/10000000000 : ℝ)|=(5265459629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539335949/1000000000 : ℝ)|^8301 ≤ (22029630139557/50000000000000 : ℝ)^6253
        have hw : |(539335949/1000000000 : ℝ)|=(539335949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s7_5 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328099649/2500000000 : ℝ)*x 0 + (-424046901/2000000000 : ℝ)*x 1 + (5393359503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328099649/2500000000 : ℝ)^8301 ≤ (21591712367071/50000000000000 : ℝ)^6253 := by
    have hnat : (1328099649 : ℕ)^8301*50000000000000^6253 ≤ 21591712367071^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328099649 2500000000 21591712367071 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424046901/2000000000 : ℝ)^8301 ≤ (12757314835017/100000000000000 : ℝ)^6253 := by
    have hnat : (424046901 : ℕ)^8301*100000000000000^6253 ≤ 12757314835017^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424046901 2000000000 12757314835017 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393359503/10000000000 : ℝ)^8301 ≤ (2689163844/6103515625 : ℝ)^6253 := by
    have hnat : (5393359503 : ℕ)^8301*6103515625^6253 ≤ 2689163844^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393359503 10000000000 2689163844 6103515625 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328099649/2500000000 : ℝ), (-424046901/2000000000 : ℝ), (5393359503/10000000000 : ℝ)] ![(21591712367071/50000000000000 : ℝ), (12757314835017/100000000000000 : ℝ), (2689163844/6103515625 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328099649/2500000000 : ℝ)|^8301 ≤ (21591712367071/50000000000000 : ℝ)^6253
        have hw : |(1328099649/2500000000 : ℝ)|=(1328099649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424046901/2000000000 : ℝ)|^8301 ≤ (12757314835017/100000000000000 : ℝ)^6253
        have hw : |(-424046901/2000000000 : ℝ)|=(424046901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393359503/10000000000 : ℝ)|^8301 ≤ (2689163844/6103515625 : ℝ)^6253
        have hw : |(5393359503/10000000000 : ℝ)|=(5393359503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s7_6 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656199291/5000000000 : ℝ)*x 0 + (1348339877/2500000000 : ℝ)*x 1 + (-530058629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656199291/5000000000 : ℝ)^8301 ≤ (21591712291533/50000000000000 : ℝ)^6253 := by
    have hnat : (2656199291 : ℕ)^8301*50000000000000^6253 ≤ 21591712291533^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656199291 5000000000 21591712291533 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348339877/2500000000 : ℝ)^8301 ≤ (44059260474319/100000000000000 : ℝ)^6253 := by
    have hnat : (1348339877 : ℕ)^8301*100000000000000^6253 ≤ 44059260474319^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348339877 2500000000 44059260474319 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530058629/2500000000 : ℝ)^8301 ≤ (12757314922881/100000000000000 : ℝ)^6253 := by
    have hnat : (530058629 : ℕ)^8301*100000000000000^6253 ≤ 12757314922881^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530058629 2500000000 12757314922881 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656199291/5000000000 : ℝ), (1348339877/2500000000 : ℝ), (-530058629/2500000000 : ℝ)] ![(21591712291533/50000000000000 : ℝ), (44059260474319/100000000000000 : ℝ), (12757314922881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656199291/5000000000 : ℝ)|^8301 ≤ (21591712291533/50000000000000 : ℝ)^6253
        have hw : |(2656199291/5000000000 : ℝ)|=(2656199291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348339877/2500000000 : ℝ)|^8301 ≤ (44059260474319/100000000000000 : ℝ)^6253
        have hw : |(1348339877/2500000000 : ℝ)|=(1348339877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-530058629/2500000000 : ℝ)|^8301 ≤ (12757314922881/100000000000000 : ℝ)^6253
        have hw : |(-530058629/2500000000 : ℝ)|=(530058629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s7_7 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369492941/10000000000 : ℝ)*x 0 + (4497714909/10000000000 : ℝ)*x 1 + (1061239313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369492941/10000000000 : ℝ)^8301 ≤ (6663371236187/20000000000000 : ℝ)^6253 := by
    have hnat : (4369492941 : ℕ)^8301*20000000000000^6253 ≤ 6663371236187^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369492941 10000000000 6663371236187 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497714909/10000000000 : ℝ)^8301 ≤ (34620941248831/100000000000000 : ℝ)^6253 := by
    have hnat : (4497714909 : ℕ)^8301*100000000000000^6253 ≤ 34620941248831^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497714909 10000000000 34620941248831 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061239313/2500000000 : ℝ)^8301 ≤ (4007775318501/12500000000000 : ℝ)^6253 := by
    have hnat : (1061239313 : ℕ)^8301*12500000000000^6253 ≤ 4007775318501^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061239313 2500000000 4007775318501 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369492941/10000000000 : ℝ), (4497714909/10000000000 : ℝ), (1061239313/2500000000 : ℝ)] ![(6663371236187/20000000000000 : ℝ), (34620941248831/100000000000000 : ℝ), (4007775318501/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369492941/10000000000 : ℝ)|^8301 ≤ (6663371236187/20000000000000 : ℝ)^6253
        have hw : |(4369492941/10000000000 : ℝ)|=(4369492941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497714909/10000000000 : ℝ)|^8301 ≤ (34620941248831/100000000000000 : ℝ)^6253
        have hw : |(4497714909/10000000000 : ℝ)|=(4497714909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061239313/2500000000 : ℝ)|^8301 ≤ (4007775318501/12500000000000 : ℝ)^6253
        have hw : |(1061239313/2500000000 : ℝ)|=(1061239313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1108_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    (11307/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1403/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (113/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (113/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (113/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (113/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (113/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (113/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (113/1000 : ℝ) ^ (2075/512 : ℝ) ≤ (7266887917628077/50000000000000000000 : ℝ) := by
    have hpowers : (113/1000 : ℝ)^2075 ≤ (7266887917628077/50000000000000000000 : ℝ)^512 := by
      have hnat : (113 : ℕ)^2075*50000000000000000000^512 ≤ 7266887917628077^512*1000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 1000 7266887917628077 50000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/1000 : ℝ)) (X := (7266887917628077/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7019/50000 : ℝ) ^ (2075/512 : ℝ) ≤ (35015040013004723/100000000000000000000 : ℝ) := by
    have hpowers : (7019/50000 : ℝ)^2075 ≤ (35015040013004723/100000000000000000000 : ℝ)^512 := by
      have hnat : (7019 : ℕ)^2075*100000000000000000000^512 ≤ 35015040013004723^512*50000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7019 50000 35015040013004723 100000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7019/50000 : ℝ)) (X := (35015040013004723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007266887917628077/25000000000000000000 : ℝ) ≤ (2500179288643909/2500000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (25007266887917628077/25000000000000000000 : ℝ)^512 ≤ (2500179288643909/2500000000000000 : ℝ)^2075 := by
      have hnat : (25007266887917628077 : ℕ)^512*2500000000000000^2075 ≤ 2500179288643909^2075*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007266887917628077 25000000000000000000 2500179288643909 2500000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500179288643909/2500000000000000 : ℝ)) (X := (25007266887917628077/25000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049548815848260877/100000000000000000000 : ℝ) ≤ (10001222374018121/10000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (100049548815848260877/100000000000000000000 : ℝ)^512 ≤ (10001222374018121/10000000000000000 : ℝ)^2075 := by
      have hnat : (100049548815848260877 : ℕ)^512*10000000000000000^2075 ≤ 10001222374018121^2075*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049548815848260877 100000000000000000000 10001222374018121 10000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001222374018121/10000000000000000 : ℝ)) (X := (100049548815848260877/100000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035015040013004723/50000000000000000000 : ℝ) ≤ (5000863796730303/5000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (50035015040013004723/50000000000000000000 : ℝ)^512 ≤ (5000863796730303/5000000000000000 : ℝ)^2075 := by
      have hnat : (50035015040013004723 : ℕ)^512*5000000000000000^2075 ≤ 5000863796730303^2075*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035015040013004723 50000000000000000000 5000863796730303 5000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000863796730303/5000000000000000 : ℝ)) (X := (50035015040013004723/50000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7266887917628077/50000000000000000000 : ℝ) ≤ ((106916193788390353/106953125000000000 : ℝ)+2*(101043888497/54760000000000 : ℝ)*(113/1000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (106916193788390353/106953125000000000 : ℝ)+2*(101043888497/54760000000000 : ℝ)*(113/1000 : ℝ)=(2500179288643909/2500000000000000 : ℝ) by norm_num, show 1+2*(7266887917628077/50000000000000000000 : ℝ)=(25007266887917628077/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35015040013004723/100000000000000000000 : ℝ)+(7266887917628077/50000000000000000000 : ℝ) ≤ ((106916193788390353/106953125000000000 : ℝ)+(101043888497/54760000000000 : ℝ)*((7019/50000 : ℝ)+(113/1000 : ℝ)))^(2075/512 : ℝ) := by
    rw [show (106916193788390353/106953125000000000 : ℝ)+(101043888497/54760000000000 : ℝ)*((7019/50000 : ℝ)+(113/1000 : ℝ))=(10001222374018121/10000000000000000 : ℝ) by norm_num, show 1+(35015040013004723/100000000000000000000 : ℝ)+(7266887917628077/50000000000000000000 : ℝ)=(100049548815848260877/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35015040013004723/100000000000000000000 : ℝ) ≤ ((106916193788390353/106953125000000000 : ℝ)+2*(101043888497/54760000000000 : ℝ)*(7019/50000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (106916193788390353/106953125000000000 : ℝ)+2*(101043888497/54760000000000 : ℝ)*(7019/50000 : ℝ)=(5000863796730303/5000000000000000 : ℝ) by norm_num, show 1+2*(35015040013004723/100000000000000000000 : ℝ)=(50035015040013004723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (106916193788390353/106953125000000000 : ℝ)*(X 1 0+X 2 0)+(101043888497/54760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (106916193788390353/106953125000000000 : ℝ)) (alpha := (101043888497/54760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (106916193788390353/106953125000000000 : ℝ)*(X 0 1+X 2 1)+(101043888497/54760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (106916193788390353/106953125000000000 : ℝ)) (alpha := (101043888497/54760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (106916193788390353/106953125000000000 : ℝ)*(X 0 2+X 1 2)+(101043888497/54760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (106916193788390353/106953125000000000 : ℝ)) (alpha := (101043888497/54760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-436649361/2000000000 : ℝ)*X 0 0+(5393683379/10000000000 : ℝ)*X 0 1+(5265136917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068976643/2000000000 : ℝ)*X 1 0+(-449691421/2000000000 : ℝ)*X 1 1+(2632568457/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672441607/5000000000 : ℝ)*X 2 0+(2632568457/5000000000 : ℝ)*X 2 1+(-2248457107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873896619/2000000000 : ℝ)*X 0 0+(424431719/1000000000 : ℝ)*X 0 1+(1124588171/2500000000 : ℝ)*X 0 2+(873896619/2000000000 : ℝ)*X 1 0+(424431719/1000000000 : ℝ)*X 1 1+(1124588171/2500000000 : ℝ)*X 1 2+(873896619/2000000000 : ℝ)*X 2 0+(424431719/1000000000 : ℝ)*X 2 1+(1124588171/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-436650359/2000000000 : ℝ)*X 0 0+(5265459629/10000000000 : ℝ)*X 0 1+(539335949/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328099649/2500000000 : ℝ)*X 1 0+(-424046901/2000000000 : ℝ)*X 1 1+(5393359503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656199291/5000000000 : ℝ)*X 2 0+(1348339877/2500000000 : ℝ)*X 2 1+(-530058629/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369492941/10000000000 : ℝ)*X 0 0+(4497714909/10000000000 : ℝ)*X 0 1+(1061239313/2500000000 : ℝ)*X 0 2+(4369492941/10000000000 : ℝ)*X 1 0+(4497714909/10000000000 : ℝ)*X 1 1+(1061239313/2500000000 : ℝ)*X 1 2+(4369492941/10000000000 : ℝ)*X 2 0+(4497714909/10000000000 : ℝ)*X 2 1+(1061239313/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96427789449854109925088013/10695312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (896859971/50000000000000 : ℝ)*(base19) + (832388217/50000000000000 : ℝ)*(base23) + (3407043/5000000000000 : ℝ)*(lower2) + (46099829/20000000000000 : ℝ)*(upper3) + (66448161/50000000000000 : ℝ)*(upper5) + (5857947834961391/100000000000000 : ℝ)*(major0) + (5857947834961391/100000000000000 : ℝ)*(major1) + (5857947834961391/100000000000000 : ℝ)*(major2) + (7779339074083151/100000000000000 : ℝ)*(sp0) + (3889692679196709/50000000000000 : ℝ)*(sp1) + (3889692743668463/50000000000000 : ℝ)*(sp2) + (246030101146649/6250000000000 : ℝ)*(sp3) + (375609611/781250000000 : ℝ)*(sp4) + (13299466637/50000000000000 : ℝ)*(sp7) + (1968254108639829/50000000000000 : ℝ)*(f.failure) + (97242339401417/1250000000000 : ℝ)*(f.sum) + (494545246227/547600000000000000000000000 : ℝ)*base66 + (1605621742005435059/85562500000000000000000000000000 : ℝ)*base67 + (705978737461814941/85562500000000000000000000000000 : ℝ)*base70 + (325560939856627441/85562500000000000000000000000000 : ℝ)*base72 + (1212356902959/2738000000000000000000000000 : ℝ)*base73 + (343636323610877441/85562500000000000000000000000000 : ℝ)*base76 + (847926958074502441/85562500000000000000000000000000 : ℝ)*base78 + (1147112300204997559/85562500000000000000000000000000 : ℝ)*base79 + (5375480515709/2738000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (78399869/5000000000000000000000 : ℝ)*base89 + (78399869/5000000000000000000000 : ℝ)*base91 + (78399869/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8605707036146971693638561/1711250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (249596683/25000000000000 : ℝ)*(base19) + (41827951/4000000000000 : ℝ)*(base23) + (55380943/50000000000000 : ℝ)*(upper3) + (6615489/20000000000000 : ℝ)*(lower4) + (27601349/25000000000000 : ℝ)*(upper5) + (235499486407769/4000000000000 : ℝ)*(major0) + (235499486407769/4000000000000 : ℝ)*(major1) + (235499486407769/4000000000000 : ℝ)*(major2) + (28023392027/100000000000000 : ℝ)*(sp1) + (28947712671/100000000000000 : ℝ)*(sp2) + (3909307836977883/50000000000000 : ℝ)*(sp4) + (488661665761063/6250000000000 : ℝ)*(sp5) + (7818585680544319/100000000000000 : ℝ)*(sp6) + (989089619700659/25000000000000 : ℝ)*(sp7) + (989089619700659/25000000000000 : ℝ)*(f.failure) + (3909307836977883/50000000000000 : ℝ)*(f.sum) + (23765321951603/2738000000000000000000000000 : ℝ)*base66 + (49891058073344719/3422500000000000000000000000000 : ℝ)*base68 + (22451129829890281/3422500000000000000000000000000 : ℝ)*base69 + (59509409455742219/3422500000000000000000000000000 : ℝ)*base72 + (13097648857937/2738000000000000000000000000 : ℝ)*base74 + (53492681579054719/3422500000000000000000000000000 : ℝ)*base76 + (4910104999619719/3422500000000000000000000000000 : ℝ)*base78 + (18530353566614719/3422500000000000000000000000000 : ℝ)*base80 + (178564578973/2738000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (32991499/2500000000000000000000 : ℝ)*base89 + (32991499/2500000000000000000000 : ℝ)*base91 + (32991499/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1108_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1108_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1108_s8_0 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-272906969/1250000000 : ℝ)*x 0 + (539360463/1000000000 : ℝ)*x 1 + (1053041917/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272906969/1250000000 : ℝ)^8301 ≤ (13263138739553/100000000000000 : ℝ)^6253 := by
    have hnat : (272906969 : ℕ)^8301*100000000000000^6253 ≤ 13263138739553^6253*1250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272906969 1250000000 13263138739553 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539360463/1000000000 : ℝ)^8301 ≤ (44061918782587/100000000000000 : ℝ)^6253 := by
    have hnat : (539360463 : ℕ)^8301*100000000000000^6253 ≤ 44061918782587^6253*1000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539360463 1000000000 44061918782587 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053041917/2000000000 : ℝ)^8301 ≤ (1333591952033/3125000000000 : ℝ)^6253 := by
    have hnat : (1053041917 : ℕ)^8301*3125000000000^6253 ≤ 1333591952033^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053041917 2000000000 1333591952033 3125000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272906969/1250000000 : ℝ), (539360463/1000000000 : ℝ), (1053041917/2000000000 : ℝ)] ![(13263138739553/100000000000000 : ℝ), (44061918782587/100000000000000 : ℝ), (1333591952033/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272906969/1250000000 : ℝ)|^8301 ≤ (13263138739553/100000000000000 : ℝ)^6253
        have hw : |(-272906969/1250000000 : ℝ)|=(272906969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539360463/1000000000 : ℝ)|^8301 ≤ (44061918782587/100000000000000 : ℝ)^6253
        have hw : |(539360463/1000000000 : ℝ)|=(539360463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053041917/2000000000 : ℝ)|^8301 ≤ (1333591952033/3125000000000 : ℝ)^6253
        have hw : |(1053041917/2000000000 : ℝ)|=(1053041917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s8_1 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344862827/10000000000 : ℝ)*x 0 + (-1124194073/5000000000 : ℝ)*x 1 + (5265209589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344862827/10000000000 : ℝ)^8301 ≤ (43534101783511/100000000000000 : ℝ)^6253 := by
    have hnat : (5344862827 : ℕ)^8301*100000000000000^6253 ≤ 43534101783511^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344862827 10000000000 43534101783511 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124194073/5000000000 : ℝ)^8301 ≤ (6895477845957/50000000000000 : ℝ)^6253 := by
    have hnat : (1124194073 : ℕ)^8301*50000000000000^6253 ≤ 6895477845957^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124194073 5000000000 6895477845957 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265209589/10000000000 : ℝ)^8301 ≤ (8534988501619/20000000000000 : ℝ)^6253 := by
    have hnat : (5265209589 : ℕ)^8301*20000000000000^6253 ≤ 8534988501619^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265209589 10000000000 8534988501619 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344862827/10000000000 : ℝ), (-1124194073/5000000000 : ℝ), (5265209589/10000000000 : ℝ)] ![(43534101783511/100000000000000 : ℝ), (6895477845957/50000000000000 : ℝ), (8534988501619/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344862827/10000000000 : ℝ)|^8301 ≤ (43534101783511/100000000000000 : ℝ)^6253
        have hw : |(5344862827/10000000000 : ℝ)|=(5344862827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1124194073/5000000000 : ℝ)|^8301 ≤ (6895477845957/50000000000000 : ℝ)^6253
        have hw : |(-1124194073/5000000000 : ℝ)|=(1124194073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265209589/10000000000 : ℝ)|^8301 ≤ (8534988501619/20000000000000 : ℝ)^6253
        have hw : |(5265209589/10000000000 : ℝ)|=(5265209589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s8_2 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068972571/2000000000 : ℝ)*x 0 + (131630239/250000000 : ℝ)*x 1 + (-2248388147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068972571/2000000000 : ℝ)^8301 ≤ (43534102086267/100000000000000 : ℝ)^6253 := by
    have hnat : (1068972571 : ℕ)^8301*100000000000000^6253 ≤ 43534102086267^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068972571 2000000000 43534102086267 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131630239/250000000 : ℝ)^8301 ≤ (8534988439213/20000000000000 : ℝ)^6253 := by
    have hnat : (131630239 : ℕ)^8301*20000000000000^6253 ≤ 8534988439213^6253*250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131630239 250000000 8534988439213 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248388147/10000000000 : ℝ)^8301 ≤ (13790955700057/100000000000000 : ℝ)^6253 := by
    have hnat : (2248388147 : ℕ)^8301*100000000000000^6253 ≤ 13790955700057^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248388147 10000000000 13790955700057 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068972571/2000000000 : ℝ), (131630239/250000000 : ℝ), (-2248388147/10000000000 : ℝ)] ![(43534102086267/100000000000000 : ℝ), (8534988439213/20000000000000 : ℝ), (13790955700057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068972571/2000000000 : ℝ)|^8301 ≤ (43534102086267/100000000000000 : ℝ)^6253
        have hw : |(1068972571/2000000000 : ℝ)|=(1068972571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131630239/250000000 : ℝ)|^8301 ≤ (8534988439213/20000000000000 : ℝ)^6253
        have hw : |(131630239/250000000 : ℝ)|=(131630239/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2248388147/10000000000 : ℝ)|^8301 ≤ (13790955700057/100000000000000 : ℝ)^6253
        have hw : |(-2248388147/10000000000 : ℝ)|=(2248388147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s8_3 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369486941/10000000000 : ℝ)*x 0 + (1061116581/2500000000 : ℝ)*x 1 + (4498202551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369486941/10000000000 : ℝ)^8301 ≤ (16658397723871/50000000000000 : ℝ)^6253 := by
    have hnat : (4369486941 : ℕ)^8301*50000000000000^6253 ≤ 16658397723871^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369486941 10000000000 16658397723871 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061116581/2500000000 : ℝ)^8301 ≤ (16028640104081/50000000000000 : ℝ)^6253 := by
    have hnat : (1061116581 : ℕ)^8301*50000000000000^6253 ≤ 16028640104081^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061116581 2500000000 16028640104081 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498202551/10000000000 : ℝ)^8301 ≤ (2164120270471/6250000000000 : ℝ)^6253 := by
    have hnat : (4498202551 : ℕ)^8301*6250000000000^6253 ≤ 2164120270471^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498202551 10000000000 2164120270471 6250000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369486941/10000000000 : ℝ), (1061116581/2500000000 : ℝ), (4498202551/10000000000 : ℝ)] ![(16658397723871/50000000000000 : ℝ), (16028640104081/50000000000000 : ℝ), (2164120270471/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369486941/10000000000 : ℝ)|^8301 ≤ (16658397723871/50000000000000 : ℝ)^6253
        have hw : |(4369486941/10000000000 : ℝ)|=(4369486941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061116581/2500000000 : ℝ)|^8301 ≤ (16028640104081/50000000000000 : ℝ)^6253
        have hw : |(1061116581/2500000000 : ℝ)|=(1061116581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498202551/10000000000 : ℝ)|^8301 ≤ (2164120270471/6250000000000 : ℝ)^6253
        have hw : |(4498202551/10000000000 : ℝ)|=(4498202551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s8_4 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183260153/10000000000 : ℝ)*x 0 + (1316382939/2500000000 : ℝ)*x 1 + (337080107/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183260153/10000000000 : ℝ)^8301 ≤ (13263174231939/100000000000000 : ℝ)^6253 := by
    have hnat : (2183260153 : ℕ)^8301*100000000000000^6253 ≤ 13263174231939^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183260153 10000000000 13263174231939 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316382939/2500000000 : ℝ)^8301 ≤ (8535681791189/20000000000000 : ℝ)^6253 := by
    have hnat : (1316382939 : ℕ)^8301*20000000000000^6253 ≤ 8535681791189^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316382939 2500000000 8535681791189 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337080107/625000000 : ℝ)^8301 ≤ (4405841679761/10000000000000 : ℝ)^6253 := by
    have hnat : (337080107 : ℕ)^8301*10000000000000^6253 ≤ 4405841679761^6253*625000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337080107 625000000 4405841679761 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183260153/10000000000 : ℝ), (1316382939/2500000000 : ℝ), (337080107/625000000 : ℝ)] ![(13263174231939/100000000000000 : ℝ), (8535681791189/20000000000000 : ℝ), (4405841679761/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183260153/10000000000 : ℝ)|^8301 ≤ (13263174231939/100000000000000 : ℝ)^6253
        have hw : |(-2183260153/10000000000 : ℝ)|=(2183260153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316382939/2500000000 : ℝ)|^8301 ≤ (8535681791189/20000000000000 : ℝ)^6253
        have hw : |(1316382939/2500000000 : ℝ)|=(1316382939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337080107/625000000 : ℝ)|^8301 ≤ (4405841679761/10000000000000 : ℝ)^6253
        have hw : |(337080107/625000000 : ℝ)|=(337080107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s8_5 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656207649/5000000000 : ℝ)*x 0 + (-424063239/2000000000 : ℝ)*x 1 + (1078656543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656207649/5000000000 : ℝ)^8301 ≤ (21591802484153/50000000000000 : ℝ)^6253 := by
    have hnat : (2656207649 : ℕ)^8301*50000000000000^6253 ≤ 21591802484153^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656207649 5000000000 21591802484153 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424063239/2000000000 : ℝ)^8301 ≤ (12757967347759/100000000000000 : ℝ)^6253 := by
    have hnat : (424063239 : ℕ)^8301*100000000000000^6253 ≤ 12757967347759^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424063239 2000000000 12757967347759 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078656543/2000000000 : ℝ)^8301 ≤ (881168553497/2000000000000 : ℝ)^6253 := by
    have hnat : (1078656543 : ℕ)^8301*2000000000000^6253 ≤ 881168553497^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078656543 2000000000 881168553497 2000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656207649/5000000000 : ℝ), (-424063239/2000000000 : ℝ), (1078656543/2000000000 : ℝ)] ![(21591802484153/50000000000000 : ℝ), (12757967347759/100000000000000 : ℝ), (881168553497/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656207649/5000000000 : ℝ)|^8301 ≤ (21591802484153/50000000000000 : ℝ)^6253
        have hw : |(2656207649/5000000000 : ℝ)|=(2656207649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424063239/2000000000 : ℝ)|^8301 ≤ (12757967347759/100000000000000 : ℝ)^6253
        have hw : |(-424063239/2000000000 : ℝ)|=(424063239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078656543/2000000000 : ℝ)|^8301 ≤ (881168553497/2000000000000 : ℝ)^6253
        have hw : |(1078656543/2000000000 : ℝ)|=(1078656543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s8_6 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312417003/10000000000 : ℝ)*x 0 + (1078656169/2000000000 : ℝ)*x 1 + (-2120316431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312417003/10000000000 : ℝ)^8301 ≤ (21591811683633/50000000000000 : ℝ)^6253 := by
    have hnat : (5312417003 : ℕ)^8301*50000000000000^6253 ≤ 21591811683633^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312417003 10000000000 21591811683633 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078656169/2000000000 : ℝ)^8301 ≤ (44058407395251/100000000000000 : ℝ)^6253 := by
    have hnat : (1078656169 : ℕ)^8301*100000000000000^6253 ≤ 44058407395251^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078656169 2000000000 44058407395251 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120316431/10000000000 : ℝ)^8301 ≤ (12757969232861/100000000000000 : ℝ)^6253 := by
    have hnat : (2120316431 : ℕ)^8301*100000000000000^6253 ≤ 12757969232861^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120316431 10000000000 12757969232861 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312417003/10000000000 : ℝ), (1078656169/2000000000 : ℝ), (-2120316431/10000000000 : ℝ)] ![(21591811683633/50000000000000 : ℝ), (44058407395251/100000000000000 : ℝ), (12757969232861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312417003/10000000000 : ℝ)|^8301 ≤ (21591811683633/50000000000000 : ℝ)^6253
        have hw : |(5312417003/10000000000 : ℝ)|=(5312417003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078656169/2000000000 : ℝ)|^8301 ≤ (44058407395251/100000000000000 : ℝ)^6253
        have hw : |(1078656169/2000000000 : ℝ)|=(1078656169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2120316431/10000000000 : ℝ)|^8301 ≤ (12757969232861/100000000000000 : ℝ)^6253
        have hw : |(-2120316431/10000000000 : ℝ)|=(2120316431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s8_7 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436949681/1000000000 : ℝ)*x 0 + (4497565979/10000000000 : ℝ)*x 1 + (1061276281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436949681/1000000000 : ℝ)^8301 ≤ (4164611917967/12500000000000 : ℝ)^6253 := by
    have hnat : (436949681 : ℕ)^8301*12500000000000^6253 ≤ 4164611917967^6253*1000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436949681 1000000000 4164611917967 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497565979/10000000000 : ℝ)^8301 ≤ (3461941940963/10000000000000 : ℝ)^6253 := by
    have hnat : (4497565979 : ℕ)^8301*10000000000000^6253 ≤ 3461941940963^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497565979 10000000000 3461941940963 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061276281/2500000000 : ℝ)^8301 ≤ (32063685238293/100000000000000 : ℝ)^6253 := by
    have hnat : (1061276281 : ℕ)^8301*100000000000000^6253 ≤ 32063685238293^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061276281 2500000000 32063685238293 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436949681/1000000000 : ℝ), (4497565979/10000000000 : ℝ), (1061276281/2500000000 : ℝ)] ![(4164611917967/12500000000000 : ℝ), (3461941940963/10000000000000 : ℝ), (32063685238293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436949681/1000000000 : ℝ)|^8301 ≤ (4164611917967/12500000000000 : ℝ)^6253
        have hw : |(436949681/1000000000 : ℝ)|=(436949681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497565979/10000000000 : ℝ)|^8301 ≤ (3461941940963/10000000000000 : ℝ)^6253
        have hw : |(4497565979/10000000000 : ℝ)|=(4497565979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061276281/2500000000 : ℝ)|^8301 ≤ (32063685238293/100000000000000 : ℝ)^6253
        have hw : |(1061276281/2500000000 : ℝ)|=(1061276281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1108_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11309/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14029/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1403/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1403/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1403/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1403/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1403/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1403/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11307/100000 : ℝ) ^ (2075/512 : ℝ) ≤ (1457029802560029/10000000000000000000 : ℝ) := by
    have hpowers : (11307/100000 : ℝ)^2075 ≤ (1457029802560029/10000000000000000000 : ℝ)^512 := by
      have hnat : (11307 : ℕ)^2075*10000000000000000000^512 ≤ 1457029802560029^512*100000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11307 100000 1457029802560029 10000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11307/100000 : ℝ)) (X := (1457029802560029/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1403/10000 : ℝ) ^ (2075/512 : ℝ) ≤ (17467120158349259/50000000000000000000 : ℝ) := by
    have hpowers : (1403/10000 : ℝ)^2075 ≤ (17467120158349259/50000000000000000000 : ℝ)^512 := by
      have hnat : (1403 : ℕ)^2075*50000000000000000000^512 ≤ 17467120158349259^512*10000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1403 10000 17467120158349259 50000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1403/10000 : ℝ)) (X := (17467120158349259/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001457029802560029/5000000000000000000 : ℝ) ≤ (2000143791305741/2000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (5001457029802560029/5000000000000000000 : ℝ)^512 ≤ (2000143791305741/2000000000000000 : ℝ)^2075 := by
      have hnat : (5001457029802560029 : ℕ)^512*2000000000000000^2075 ≤ 2000143791305741^2075*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001457029802560029 5000000000000000000 2000143791305741 2000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000143791305741/2000000000000000 : ℝ)) (X := (5001457029802560029/5000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506188067292787351/12500000000000000000 : ℝ) ≤ (10001221281891403/10000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (12506188067292787351/12500000000000000000 : ℝ)^512 ≤ (10001221281891403/10000000000000000 : ℝ)^2075 := by
      have hnat : (12506188067292787351 : ℕ)^512*10000000000000000^2075 ≤ 10001221281891403^2075*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506188067292787351 12500000000000000000 10001221281891403 10000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001221281891403/10000000000000000 : ℝ)) (X := (12506188067292787351/12500000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017467120158349259/25000000000000000000 : ℝ) ≤ (10001723607254101/10000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (25017467120158349259/25000000000000000000 : ℝ)^512 ≤ (10001723607254101/10000000000000000 : ℝ)^2075 := by
      have hnat : (25017467120158349259 : ℕ)^512*10000000000000000^2075 ≤ 10001723607254101^2075*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017467120158349259 25000000000000000000 10001723607254101 10000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001723607254101/10000000000000000 : ℝ)) (X := (25017467120158349259/25000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1457029802560029/10000000000000000000 : ℝ) ≤ ((27220598132875611143/27230000000000000000 : ℝ)+2*(251162681349/136150000000000 : ℝ)*(11307/100000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (27220598132875611143/27230000000000000000 : ℝ)+2*(251162681349/136150000000000 : ℝ)*(11307/100000 : ℝ)=(2000143791305741/2000000000000000 : ℝ) by norm_num, show 1+2*(1457029802560029/10000000000000000000 : ℝ)=(5001457029802560029/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17467120158349259/50000000000000000000 : ℝ)+(1457029802560029/10000000000000000000 : ℝ) ≤ ((27220598132875611143/27230000000000000000 : ℝ)+(251162681349/136150000000000 : ℝ)*((1403/10000 : ℝ)+(11307/100000 : ℝ)))^(2075/512 : ℝ) := by
    rw [show (27220598132875611143/27230000000000000000 : ℝ)+(251162681349/136150000000000 : ℝ)*((1403/10000 : ℝ)+(11307/100000 : ℝ))=(10001221281891403/10000000000000000 : ℝ) by norm_num, show 1+(17467120158349259/50000000000000000000 : ℝ)+(1457029802560029/10000000000000000000 : ℝ)=(12506188067292787351/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17467120158349259/50000000000000000000 : ℝ) ≤ ((27220598132875611143/27230000000000000000 : ℝ)+2*(251162681349/136150000000000 : ℝ)*(1403/10000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (27220598132875611143/27230000000000000000 : ℝ)+2*(251162681349/136150000000000 : ℝ)*(1403/10000 : ℝ)=(10001723607254101/10000000000000000 : ℝ) by norm_num, show 1+2*(17467120158349259/50000000000000000000 : ℝ)=(25017467120158349259/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27220598132875611143/27230000000000000000 : ℝ)*(X 1 0+X 2 0)+(251162681349/136150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (27220598132875611143/27230000000000000000 : ℝ)) (alpha := (251162681349/136150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27220598132875611143/27230000000000000000 : ℝ)*(X 0 1+X 2 1)+(251162681349/136150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (27220598132875611143/27230000000000000000 : ℝ)) (alpha := (251162681349/136150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27220598132875611143/27230000000000000000 : ℝ)*(X 0 2+X 1 2)+(251162681349/136150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (27220598132875611143/27230000000000000000 : ℝ)) (alpha := (251162681349/136150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-272906969/1250000000 : ℝ)*X 0 0+(539360463/1000000000 : ℝ)*X 0 1+(1053041917/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344862827/10000000000 : ℝ)*X 1 0+(-1124194073/5000000000 : ℝ)*X 1 1+(5265209589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068972571/2000000000 : ℝ)*X 2 0+(131630239/250000000 : ℝ)*X 2 1+(-2248388147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369486941/10000000000 : ℝ)*X 0 0+(1061116581/2500000000 : ℝ)*X 0 1+(4498202551/10000000000 : ℝ)*X 0 2+(4369486941/10000000000 : ℝ)*X 1 0+(1061116581/2500000000 : ℝ)*X 1 1+(4498202551/10000000000 : ℝ)*X 1 2+(4369486941/10000000000 : ℝ)*X 2 0+(1061116581/2500000000 : ℝ)*X 2 1+(4498202551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2183260153/10000000000 : ℝ)*X 0 0+(1316382939/2500000000 : ℝ)*X 0 1+(337080107/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656207649/5000000000 : ℝ)*X 1 0+(-424063239/2000000000 : ℝ)*X 1 1+(1078656543/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312417003/10000000000 : ℝ)*X 2 0+(1078656169/2000000000 : ℝ)*X 2 1+(-2120316431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436949681/1000000000 : ℝ)*X 0 0+(4497565979/10000000000 : ℝ)*X 0 1+(1061276281/2500000000 : ℝ)*X 0 2+(436949681/1000000000 : ℝ)*X 1 0+(4497565979/10000000000 : ℝ)*X 1 1+(1061276281/2500000000 : ℝ)*X 1 2+(436949681/1000000000 : ℝ)*X 2 0+(4497565979/10000000000 : ℝ)*X 2 1+(1061276281/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29654947750197041078551689/6078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (233044311/25000000000000 : ℝ)*(base19) + (927717917/100000000000000 : ℝ)*(base23) + (4838257/20000000000000 : ℝ)*(lower2) + (115549693/100000000000000 : ℝ)*(upper3) + (4396523/5000000000000 : ℝ)*(upper5) + (183275635702163/3125000000000 : ℝ)*(major0) + (183275635702163/3125000000000 : ℝ)*(major1) + (183275635702163/3125000000000 : ℝ)*(major2) + (7788488335029517/100000000000000 : ℝ)*(sp0) + (243391033943757/3125000000000 : ℝ)*(sp1) + (7788513090659551/100000000000000 : ℝ)*(sp2) + (1970556507936877/50000000000000 : ℝ)*(sp3) + (1605209247/6250000000000 : ℝ)*(sp4) + (13488055097/100000000000000 : ℝ)*(sp7) + (78822530078577/2000000000000 : ℝ)*(f.failure) + (1947128504594367/25000000000000 : ℝ)*(f.sum) + (2442576458323/3403750000000000000000000000 : ℝ)*base66 + (1260262271444441441/85093750000000000000000000000000 : ℝ)*base68 + (83265497130246059/85093750000000000000000000000000 : ℝ)*base69 + (326316853753277309/85093750000000000000000000000000 : ℝ)*base71 + (86987259751557/13615000000000000000000000000 : ℝ)*base74 + (393162156653964809/85093750000000000000000000000000 : ℝ)*base75 + (325008140797066441/85093750000000000000000000000000 : ℝ)*base78 + (3088106628062621059/85093750000000000000000000000000 : ℝ)*base79 + (9599067813507/13615000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1167097/200000000000000000000 : ℝ)*base89 + (1167097/200000000000000000000 : ℝ)*base91 + (1167097/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21790538613810062819228102841/1361500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1702535833/100000000000000 : ℝ)*(base23) + (441528587/100000000000000 : ℝ)*(lower1) + (462155833/100000000000000 : ℝ)*(lower2) + (4728129/10000000000000 : ℝ)*(upper3) + (2676173/2500000000000 : ℝ)*(lower4) + (15467/7812500000 : ℝ)*(upper5) + (5894402240781543/100000000000000 : ℝ)*(major0) + (5894402240781543/100000000000000 : ℝ)*(major1) + (5894402240781543/100000000000000 : ℝ)*(major2) + (5784162697/25000000000000 : ℝ)*(sp1) + (7827798573746263/100000000000000 : ℝ)*(sp4) + (313111017483819/4000000000000 : ℝ)*(sp5) + (782779687121043/10000000000000 : ℝ)*(sp6) + (990251343580849/25000000000000 : ℝ)*(sp7) + (990251343580849/25000000000000 : ℝ)*(f.failure) + (7827798573746263/100000000000000 : ℝ)*(f.sum) + (34178783930401/13615000000000000000000000000 : ℝ)*base66 + (23685172977795066351/2723000000000000000000000000000000 : ℝ)*base68 + (16588084236899066351/2723000000000000000000000000000000 : ℝ)*base70 + (56306790512497066351/2723000000000000000000000000000000 : ℝ)*base72 + (33076778886751/13615000000000000000000000000 : ℝ)*base74 + (38039819695122066351/2723000000000000000000000000000000 : ℝ)*base76 + (11063892447769066351/2723000000000000000000000000000000 : ℝ)*base78 + (73707732754201066351/2723000000000000000000000000000000 : ℝ)*base80 + (11825735992501/3403750000000000000000000000 : ℝ)*base81 + (29716089/2500000000000000000000 : ℝ)*base89 + (29716089/2500000000000000000000 : ℝ)*base91 + (29716089/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1108_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1108_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1108_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1108_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1108_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1108_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1108_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
