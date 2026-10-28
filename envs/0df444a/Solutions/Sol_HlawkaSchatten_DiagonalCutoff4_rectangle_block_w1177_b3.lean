-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1177_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:48:22.863183+00:00
-- url     : https://prove2.me/submissions/6958e47e-188a-473b-b4da-ecda047943ed

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
theorem support_rectangle_w1177_s9_0 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668075819/1250000000 : ℝ)*x 0 + (5266336649/10000000000 : ℝ)*x 1 + (-221416833/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668075819/1250000000 : ℝ)^4185 ≤ (43628929371361/100000000000000 : ℝ)^3161 := by
    have hnat : (668075819 : ℕ)^4185*100000000000000^3161 ≤ 43628929371361^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668075819 1250000000 43628929371361 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266336649/10000000000 : ℝ)^4185 ≤ (5348128970487/12500000000000 : ℝ)^3161 := by
    have hnat : (5266336649 : ℕ)^4185*12500000000000^3161 ≤ 5348128970487^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266336649 10000000000 5348128970487 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221416833/1000000000 : ℝ)^4185 ≤ (6793019426153/50000000000000 : ℝ)^3161 := by
    have hnat : (221416833 : ℕ)^4185*50000000000000^3161 ≤ 6793019426153^3161*1000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221416833 1000000000 6793019426153 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668075819/1250000000 : ℝ), (5266336649/10000000000 : ℝ), (-221416833/1000000000 : ℝ)] ![(43628929371361/100000000000000 : ℝ), (5348128970487/12500000000000 : ℝ), (6793019426153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668075819/1250000000 : ℝ)|^4185 ≤ (43628929371361/100000000000000 : ℝ)^3161
        have hw : |(668075819/1250000000 : ℝ)|=(668075819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266336649/10000000000 : ℝ)|^4185 ≤ (5348128970487/12500000000000 : ℝ)^3161
        have hw : |(5266336649/10000000000 : ℝ)|=(5266336649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221416833/1000000000 : ℝ)|^4185 ≤ (6793019426153/50000000000000 : ℝ)^3161
        have hw : |(-221416833/1000000000 : ℝ)|=(221416833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s9_1 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215026617/1000000000 : ℝ)*x 0 + (5266653091/10000000000 : ℝ)*x 1 + (5392030491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215026617/1000000000 : ℝ)^4185 ≤ (13069360396713/100000000000000 : ℝ)^3161 := by
    have hnat : (215026617 : ℕ)^4185*100000000000000^3161 ≤ 13069360396713^3161*1000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215026617 1000000000 13069360396713 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266653091/10000000000 : ℝ)^4185 ≤ (4278843547393/10000000000000 : ℝ)^3161 := by
    have hnat : (5266653091 : ℕ)^4185*10000000000000^3161 ≤ 4278843547393^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266653091 10000000000 4278843547393 10000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392030491/10000000000 : ℝ)^4185 ≤ (11035551029901/25000000000000 : ℝ)^3161 := by
    have hnat : (5392030491 : ℕ)^4185*25000000000000^3161 ≤ 11035551029901^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392030491 10000000000 11035551029901 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215026617/1000000000 : ℝ), (5266653091/10000000000 : ℝ), (5392030491/10000000000 : ℝ)] ![(13069360396713/100000000000000 : ℝ), (4278843547393/10000000000000 : ℝ), (11035551029901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215026617/1000000000 : ℝ)|^4185 ≤ (13069360396713/100000000000000 : ℝ)^3161
        have hw : |(-215026617/1000000000 : ℝ)|=(215026617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266653091/10000000000 : ℝ)|^4185 ≤ (4278843547393/10000000000000 : ℝ)^3161
        have hw : |(5266653091/10000000000 : ℝ)|=(5266653091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392030491/10000000000 : ℝ)|^4185 ≤ (11035551029901/25000000000000 : ℝ)^3161
        have hw : |(5392030491/10000000000 : ℝ)|=(5392030491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s9_2 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312600083/10000000000 : ℝ)*x 0 + (-130529583/625000000 : ℝ)*x 1 + (67400381/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312600083/10000000000 : ℝ)^4185 ≤ (43283351829703/100000000000000 : ℝ)^3161 := by
    have hnat : (5312600083 : ℕ)^4185*100000000000000^3161 ≤ 43283351829703^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312600083 10000000000 43283351829703 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130529583/625000000 : ℝ)^4185 ≤ (628722207761/5000000000000 : ℝ)^3161 := by
    have hnat : (130529583 : ℕ)^4185*5000000000000^3161 ≤ 628722207761^3161*625000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130529583 625000000 628722207761 5000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67400381/125000000 : ℝ)^4185 ≤ (44142204000379/100000000000000 : ℝ)^3161 := by
    have hnat : (67400381 : ℕ)^4185*100000000000000^3161 ≤ 44142204000379^3161*125000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67400381 125000000 44142204000379 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312600083/10000000000 : ℝ), (-130529583/625000000 : ℝ), (67400381/125000000 : ℝ)] ![(43283351829703/100000000000000 : ℝ), (628722207761/5000000000000 : ℝ), (44142204000379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312600083/10000000000 : ℝ)|^4185 ≤ (43283351829703/100000000000000 : ℝ)^3161
        have hw : |(5312600083/10000000000 : ℝ)|=(5312600083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130529583/625000000 : ℝ)|^4185 ≤ (628722207761/5000000000000 : ℝ)^3161
        have hw : |(-130529583/625000000 : ℝ)|=(130529583/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67400381/125000000 : ℝ)|^4185 ≤ (44142204000379/100000000000000 : ℝ)^3161
        have hw : |(67400381/125000000 : ℝ)|=(67400381/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s9_3 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312600143/10000000000 : ℝ)*x 0 + (5392030507/10000000000 : ℝ)*x 1 + (-208847321/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312600143/10000000000 : ℝ)^4185 ≤ (43283352476899/100000000000000 : ℝ)^3161 := by
    have hnat : (5312600143 : ℕ)^4185*100000000000000^3161 ≤ 43283352476899^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312600143 10000000000 43283352476899 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392030507/10000000000 : ℝ)^4185 ≤ (44142204293021/100000000000000 : ℝ)^3161 := by
    have hnat : (5392030507 : ℕ)^4185*100000000000000^3161 ≤ 44142204293021^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392030507 10000000000 44142204293021 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208847321/1000000000 : ℝ)^4185 ≤ (12574443214603/100000000000000 : ℝ)^3161 := by
    have hnat : (208847321 : ℕ)^4185*100000000000000^3161 ≤ 12574443214603^3161*1000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208847321 1000000000 12574443214603 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312600143/10000000000 : ℝ), (5392030507/10000000000 : ℝ), (-208847321/1000000000 : ℝ)] ![(43283352476899/100000000000000 : ℝ), (44142204293021/100000000000000 : ℝ), (12574443214603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312600143/10000000000 : ℝ)|^4185 ≤ (43283352476899/100000000000000 : ℝ)^3161
        have hw : |(5312600143/10000000000 : ℝ)|=(5312600143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392030507/10000000000 : ℝ)|^4185 ≤ (44142204293021/100000000000000 : ℝ)^3161
        have hw : |(5392030507/10000000000 : ℝ)|=(5392030507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208847321/1000000000 : ℝ)|^4185 ≤ (12574443214603/100000000000000 : ℝ)^3161
        have hw : |(-208847321/1000000000 : ℝ)|=(208847321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s9_4 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272486111/625000000 : ℝ)*x 0 + (4487146653/10000000000 : ℝ)*x 1 + (529499739/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272486111/625000000 : ℝ)^4185 ≤ (16658638865659/50000000000000 : ℝ)^3161 := by
    have hnat : (272486111 : ℕ)^4185*50000000000000^3161 ≤ 16658638865659^3161*625000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272486111 625000000 16658638865659 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487146653/10000000000 : ℝ)^4185 ≤ (276895994121/800000000000 : ℝ)^3161 := by
    have hnat : (4487146653 : ℕ)^4185*800000000000^3161 ≤ 276895994121^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487146653 10000000000 276895994121 800000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529499739/1250000000 : ℝ)^4185 ≤ (3207072299473/10000000000000 : ℝ)^3161 := by
    have hnat : (529499739 : ℕ)^4185*10000000000000^3161 ≤ 3207072299473^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529499739 1250000000 3207072299473 10000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272486111/625000000 : ℝ), (4487146653/10000000000 : ℝ), (529499739/1250000000 : ℝ)] ![(16658638865659/50000000000000 : ℝ), (276895994121/800000000000 : ℝ), (3207072299473/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272486111/625000000 : ℝ)|^4185 ≤ (16658638865659/50000000000000 : ℝ)^3161
        have hw : |(272486111/625000000 : ℝ)|=(272486111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487146653/10000000000 : ℝ)|^4185 ≤ (276895994121/800000000000 : ℝ)^3161
        have hw : |(4487146653/10000000000 : ℝ)|=(4487146653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529499739/1250000000 : ℝ)|^4185 ≤ (3207072299473/10000000000000 : ℝ)^3161
        have hw : |(529499739/1250000000 : ℝ)|=(529499739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1177_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11399/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3517/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11399/100000 : ℝ) ^ (8369/2048 : ℝ) ≤ (13994454904180333/100000000000000000000 : ℝ) := by
    have hpowers : (11399/100000 : ℝ)^8369 ≤ (13994454904180333/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11399 : ℕ)^8369*100000000000000000000^2048 ≤ 13994454904180333^2048*100000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11399 100000 13994454904180333 100000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11399/100000 : ℝ)) (X := (13994454904180333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14069/100000 : ℝ) ^ (8369/2048 : ℝ) ≤ (3307051078209189/10000000000000000000 : ℝ) := by
    have hpowers : (14069/100000 : ℝ)^8369 ≤ (3307051078209189/10000000000000000000 : ℝ)^2048 := by
      have hnat : (14069 : ℕ)^8369*10000000000000000000^2048 ≤ 3307051078209189^2048*100000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14069 100000 3307051078209189 10000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14069/100000 : ℝ)) (X := (3307051078209189/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013994454904180333/50000000000000000000 : ℝ) ≤ (5000342425794683/5000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (50013994454904180333/50000000000000000000 : ℝ)^2048 ≤ (5000342425794683/5000000000000000 : ℝ)^8369 := by
      have hnat : (50013994454904180333 : ℕ)^2048*5000000000000000^8369 ≤ 5000342425794683^8369*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013994454904180333 50000000000000000000 5000342425794683 5000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000342425794683/5000000000000000 : ℝ)) (X := (50013994454904180333/50000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047064965686272223/100000000000000000000 : ℝ) ≤ (10001151534501819/10000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (100047064965686272223/100000000000000000000 : ℝ)^2048 ≤ (10001151534501819/10000000000000000 : ℝ)^8369 := by
      have hnat : (100047064965686272223 : ℕ)^2048*10000000000000000^8369 ≤ 10001151534501819^8369*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047064965686272223 100000000000000000000 10001151534501819 10000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001151534501819/10000000000000000 : ℝ)) (X := (100047064965686272223/100000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003307051078209189/5000000000000000000 : ℝ) ≤ (78137642323549/78125000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (5003307051078209189/5000000000000000000 : ℝ)^2048 ≤ (78137642323549/78125000000000 : ℝ)^8369 := by
      have hnat : (5003307051078209189 : ℕ)^2048*78125000000000^8369 ≤ 78137642323549^8369*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003307051078209189 5000000000000000000 78137642323549 78125000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78137642323549/78125000000000 : ℝ)) (X := (5003307051078209189/5000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13994454904180333/100000000000000000000 : ℝ) ≤ ((13345594558352751863/13350000000000000000 : ℝ)+2*(466682912453/267000000000000 : ℝ)*(11399/100000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (13345594558352751863/13350000000000000000 : ℝ)+2*(466682912453/267000000000000 : ℝ)*(11399/100000 : ℝ)=(5000342425794683/5000000000000000 : ℝ) by norm_num, show 1+2*(13994454904180333/100000000000000000000 : ℝ)=(50013994454904180333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3307051078209189/10000000000000000000 : ℝ)+(13994454904180333/100000000000000000000 : ℝ) ≤ ((13345594558352751863/13350000000000000000 : ℝ)+(466682912453/267000000000000 : ℝ)*((14069/100000 : ℝ)+(11399/100000 : ℝ)))^(8369/2048 : ℝ) := by
    rw [show (13345594558352751863/13350000000000000000 : ℝ)+(466682912453/267000000000000 : ℝ)*((14069/100000 : ℝ)+(11399/100000 : ℝ))=(10001151534501819/10000000000000000 : ℝ) by norm_num, show 1+(3307051078209189/10000000000000000000 : ℝ)+(13994454904180333/100000000000000000000 : ℝ)=(100047064965686272223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3307051078209189/10000000000000000000 : ℝ) ≤ ((13345594558352751863/13350000000000000000 : ℝ)+2*(466682912453/267000000000000 : ℝ)*(14069/100000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (13345594558352751863/13350000000000000000 : ℝ)+2*(466682912453/267000000000000 : ℝ)*(14069/100000 : ℝ)=(78137642323549/78125000000000 : ℝ) by norm_num, show 1+2*(3307051078209189/10000000000000000000 : ℝ)=(5003307051078209189/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13345594558352751863/13350000000000000000 : ℝ)*(X 1 0+X 2 0)+(466682912453/267000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (13345594558352751863/13350000000000000000 : ℝ)) (alpha := (466682912453/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13345594558352751863/13350000000000000000 : ℝ)*(X 0 1+X 2 1)+(466682912453/267000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (13345594558352751863/13350000000000000000 : ℝ)) (alpha := (466682912453/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13345594558352751863/13350000000000000000 : ℝ)*(X 0 2+X 1 2)+(466682912453/267000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (13345594558352751863/13350000000000000000 : ℝ)) (alpha := (466682912453/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((668075819/1250000000 : ℝ)*X 2 0+(5266336649/10000000000 : ℝ)*X 2 1+(-221416833/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-215026617/1000000000 : ℝ)*X 0 0+(5266653091/10000000000 : ℝ)*X 0 1+(5392030491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312600083/10000000000 : ℝ)*X 1 0+(-130529583/625000000 : ℝ)*X 1 1+(67400381/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312600143/10000000000 : ℝ)*X 2 0+(5392030507/10000000000 : ℝ)*X 2 1+(-208847321/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((272486111/625000000 : ℝ)*X 0 0+(4487146653/10000000000 : ℝ)*X 0 1+(529499739/1250000000 : ℝ)*X 0 2+(272486111/625000000 : ℝ)*X 1 0+(4487146653/10000000000 : ℝ)*X 1 1+(529499739/1250000000 : ℝ)*X 1 2+(272486111/625000000 : ℝ)*X 2 0+(4487146653/10000000000 : ℝ)*X 2 1+(529499739/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (138107901981301242017921667/55625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (765016651/100000000000000 : ℝ)*(base19) + (472757771/50000000000000 : ℝ)*(base23) + (28493907/12500000000000 : ℝ)*(lower1) + (87773/625000000000 : ℝ)*(upper2) + (57896297/50000000000000 : ℝ)*(upper3) + (7803473/10000000000000 : ℝ)*(upper5) + (1494699607942309/25000000000000 : ℝ)*(major0) + (1494699607942309/25000000000000 : ℝ)*(major1) + (1494699607942309/25000000000000 : ℝ)*(major2) + (10620612419/100000000000000 : ℝ)*(sp0) + (996987526033281/12500000000000 : ℝ)*(sp1) + (7975899443249597/100000000000000 : ℝ)*(sp2) + (7975888642138287/100000000000000 : ℝ)*(sp3) + (1990848286255461/50000000000000 : ℝ)*(sp4) + (1990848286255461/50000000000000 : ℝ)*(f.failure) + (996987526033281/12500000000000 : ℝ)*(f.sum) + (12166049529823/3337500000000000000000000000 : ℝ)*base66 + (1033558758934126111/111250000000000000000000000000000 : ℝ)*base68 + (1228537998788373889/111250000000000000000000000000000 : ℝ)*base69 + (2082798603460376111/111250000000000000000000000000000 : ℝ)*base72 + (5501224986449/1668750000000000000000000000 : ℝ)*base74 + (359725695678373889/111250000000000000000000000000000 : ℝ)*base75 + (1790214193762876111/111250000000000000000000000000000 : ℝ)*base78 + (1861346965944126111/111250000000000000000000000000000 : ℝ)*base80 + (100590689044873/3337500000000000000000000000 : ℝ)*base82 + (30096869/2500000000000000000000 : ℝ)*base89 + (30096869/2500000000000000000000 : ℝ)*base91 + (30096869/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1177_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1177_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1177_box_0 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2024517699/10000000000 : ℝ)*x 0 + (5375804509/10000000000 : ℝ)*x 1 + (2687901077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2024517699/10000000000 : ℝ)^4185 ≤ (482687164219/4000000000000 : ℝ)^3161 := by
    have hnat : (2024517699 : ℕ)^4185*4000000000000^3161 ≤ 482687164219^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024517699 10000000000 482687164219 4000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375804509/10000000000 : ℝ)^4185 ≤ (21983211595981/50000000000000 : ℝ)^3161 := by
    have hnat : (5375804509 : ℕ)^4185*50000000000000^3161 ≤ 21983211595981^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375804509 10000000000 21983211595981 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687901077/5000000000 : ℝ)^4185 ≤ (43966397692001/100000000000000 : ℝ)^3161 := by
    have hnat : (2687901077 : ℕ)^4185*100000000000000^3161 ≤ 43966397692001^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687901077 5000000000 43966397692001 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2024517699/10000000000 : ℝ), (5375804509/10000000000 : ℝ), (2687901077/5000000000 : ℝ)] ![(482687164219/4000000000000 : ℝ), (21983211595981/50000000000000 : ℝ), (43966397692001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2024517699/10000000000 : ℝ)|^4185 ≤ (482687164219/4000000000000 : ℝ)^3161
        have hw : |(-2024517699/10000000000 : ℝ)|=(2024517699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375804509/10000000000 : ℝ)|^4185 ≤ (21983211595981/50000000000000 : ℝ)^3161
        have hw : |(5375804509/10000000000 : ℝ)|=(5375804509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687901077/5000000000 : ℝ)|^4185 ≤ (43966397692001/100000000000000 : ℝ)^3161
        have hw : |(2687901077/5000000000 : ℝ)|=(2687901077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_1 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662036871/1250000000 : ℝ)*x 0 + (-1066214621/5000000000 : ℝ)*x 1 + (5375803967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662036871/1250000000 : ℝ)^4185 ≤ (43107562507099/100000000000000 : ℝ)^3161 := by
    have hnat : (662036871 : ℕ)^4185*100000000000000^3161 ≤ 43107562507099^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662036871 1250000000 43107562507099 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066214621/5000000000 : ℝ)^4185 ≤ (3231505039231/25000000000000 : ℝ)^3161 := by
    have hnat : (1066214621 : ℕ)^4185*25000000000000^3161 ≤ 3231505039231^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066214621 5000000000 3231505039231 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375803967/10000000000 : ℝ)^4185 ≤ (2198320866159/5000000000000 : ℝ)^3161 := by
    have hnat : (5375803967 : ℕ)^4185*5000000000000^3161 ≤ 2198320866159^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375803967 10000000000 2198320866159 5000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662036871/1250000000 : ℝ), (-1066214621/5000000000 : ℝ), (5375803967/10000000000 : ℝ)] ![(43107562507099/100000000000000 : ℝ), (3231505039231/25000000000000 : ℝ), (2198320866159/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662036871/1250000000 : ℝ)|^4185 ≤ (43107562507099/100000000000000 : ℝ)^3161
        have hw : |(662036871/1250000000 : ℝ)|=(662036871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1066214621/5000000000 : ℝ)|^4185 ≤ (3231505039231/25000000000000 : ℝ)^3161
        have hw : |(-1066214621/5000000000 : ℝ)|=(1066214621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375803967/10000000000 : ℝ)|^4185 ≤ (2198320866159/5000000000000 : ℝ)^3161
        have hw : |(5375803967/10000000000 : ℝ)|=(5375803967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_2 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296295843/10000000000 : ℝ)*x 0 + (1075160557/2000000000 : ℝ)*x 1 + (-2132429661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296295843/10000000000 : ℝ)^4185 ≤ (43107571935983/100000000000000 : ℝ)^3161 := by
    have hnat : (5296295843 : ℕ)^4185*100000000000000^3161 ≤ 43107571935983^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296295843 10000000000 43107571935983 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075160557/2000000000 : ℝ)^4185 ≤ (21983202262237/50000000000000 : ℝ)^3161 := by
    have hnat : (1075160557 : ℕ)^4185*50000000000000^3161 ≤ 21983202262237^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075160557 2000000000 21983202262237 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132429661/10000000000 : ℝ)^4185 ≤ (3231505879881/25000000000000 : ℝ)^3161 := by
    have hnat : (2132429661 : ℕ)^4185*25000000000000^3161 ≤ 3231505879881^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132429661 10000000000 3231505879881 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296295843/10000000000 : ℝ), (1075160557/2000000000 : ℝ), (-2132429661/10000000000 : ℝ)] ![(43107571935983/100000000000000 : ℝ), (21983202262237/50000000000000 : ℝ), (3231505879881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296295843/10000000000 : ℝ)|^4185 ≤ (43107571935983/100000000000000 : ℝ)^3161
        have hw : |(5296295843/10000000000 : ℝ)|=(5296295843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075160557/2000000000 : ℝ)|^4185 ≤ (21983202262237/50000000000000 : ℝ)^3161
        have hw : |(1075160557/2000000000 : ℝ)|=(1075160557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132429661/10000000000 : ℝ)|^4185 ≤ (3231505879881/25000000000000 : ℝ)^3161
        have hw : |(-2132429661/10000000000 : ℝ)|=(2132429661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_3 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4466942241/10000000000 : ℝ)*x 0 + (4308264383/10000000000 : ℝ)*x 1 + (4308265393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4466942241/10000000000 : ℝ)^4185 ≤ (8601453642541/25000000000000 : ℝ)^3161 := by
    have hnat : (4466942241 : ℕ)^4185*25000000000000^3161 ≤ 8601453642541^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4466942241 10000000000 8601453642541 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4308264383/10000000000 : ℝ)^4185 ≤ (3279708762011/10000000000000 : ℝ)^3161 := by
    have hnat : (4308264383 : ℕ)^4185*10000000000000^3161 ≤ 3279708762011^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308264383 10000000000 3279708762011 10000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4308265393/10000000000 : ℝ)^4185 ≤ (32797097799583/100000000000000 : ℝ)^3161 := by
    have hnat : (4308265393 : ℕ)^4185*100000000000000^3161 ≤ 32797097799583^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308265393 10000000000 32797097799583 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4466942241/10000000000 : ℝ), (4308264383/10000000000 : ℝ), (4308265393/10000000000 : ℝ)] ![(8601453642541/25000000000000 : ℝ), (3279708762011/10000000000000 : ℝ), (32797097799583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4466942241/10000000000 : ℝ)|^4185 ≤ (8601453642541/25000000000000 : ℝ)^3161
        have hw : |(4466942241/10000000000 : ℝ)|=(4466942241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4308264383/10000000000 : ℝ)|^4185 ≤ (3279708762011/10000000000000 : ℝ)^3161
        have hw : |(4308264383/10000000000 : ℝ)|=(4308264383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4308265393/10000000000 : ℝ)|^4185 ≤ (32797097799583/100000000000000 : ℝ)^3161
        have hw : |(4308265393/10000000000 : ℝ)|=(4308265393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_4 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-455478841/2000000000 : ℝ)*x 0 + (5281572251/10000000000 : ℝ)*x 1 + (2640786383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (455478841/2000000000 : ℝ)^4185 ≤ (14102026590849/100000000000000 : ℝ)^3161 := by
    have hnat : (455478841 : ℕ)^4185*100000000000000^3161 ≤ 14102026590849^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455478841 2000000000 14102026590849 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281572251/10000000000 : ℝ)^4185 ≤ (2147449196409/5000000000000 : ℝ)^3161 := by
    have hnat : (5281572251 : ℕ)^4185*5000000000000^3161 ≤ 2147449196409^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281572251 10000000000 2147449196409 5000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640786383/5000000000 : ℝ)^4185 ≤ (171795957891/400000000000 : ℝ)^3161 := by
    have hnat : (2640786383 : ℕ)^4185*400000000000^3161 ≤ 171795957891^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640786383 5000000000 171795957891 400000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-455478841/2000000000 : ℝ), (5281572251/10000000000 : ℝ), (2640786383/5000000000 : ℝ)] ![(14102026590849/100000000000000 : ℝ), (2147449196409/5000000000000 : ℝ), (171795957891/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-455478841/2000000000 : ℝ)|^4185 ≤ (14102026590849/100000000000000 : ℝ)^3161
        have hw : |(-455478841/2000000000 : ℝ)|=(455478841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281572251/10000000000 : ℝ)|^4185 ≤ (2147449196409/5000000000000 : ℝ)^3161
        have hw : |(5281572251/10000000000 : ℝ)|=(5281572251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640786383/5000000000 : ℝ)|^4185 ≤ (171795957891/400000000000 : ℝ)^3161
        have hw : |(2640786383/5000000000 : ℝ)|=(2640786383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_5 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340704601/2500000000 : ℝ)*x 0 + (-2169598029/10000000000 : ℝ)*x 1 + (211262897/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340704601/2500000000 : ℝ)^4185 ≤ (10956466142461/25000000000000 : ℝ)^3161 := by
    have hnat : (1340704601 : ℕ)^4185*25000000000000^3161 ≤ 10956466142461^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340704601 2500000000 10956466142461 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2169598029/10000000000 : ℝ)^4185 ≤ (529005984493/4000000000000 : ℝ)^3161 := by
    have hnat : (2169598029 : ℕ)^4185*4000000000000^3161 ≤ 529005984493^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169598029 10000000000 529005984493 4000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211262897/400000000 : ℝ)^4185 ≤ (42948985801491/100000000000000 : ℝ)^3161 := by
    have hnat : (211262897 : ℕ)^4185*100000000000000^3161 ≤ 42948985801491^3161*400000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211262897 400000000 42948985801491 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340704601/2500000000 : ℝ), (-2169598029/10000000000 : ℝ), (211262897/400000000 : ℝ)] ![(10956466142461/25000000000000 : ℝ), (529005984493/4000000000000 : ℝ), (42948985801491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340704601/2500000000 : ℝ)|^4185 ≤ (10956466142461/25000000000000 : ℝ)^3161
        have hw : |(1340704601/2500000000 : ℝ)|=(1340704601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2169598029/10000000000 : ℝ)|^4185 ≤ (529005984493/4000000000000 : ℝ)^3161
        have hw : |(-2169598029/10000000000 : ℝ)|=(2169598029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211262897/400000000 : ℝ)|^4185 ≤ (42948985801491/100000000000000 : ℝ)^3161
        have hw : |(211262897/400000000 : ℝ)|=(211262897/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_6 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681409091/5000000000 : ℝ)*x 0 + (211262899/400000000 : ℝ)*x 1 + (-108479913/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681409091/5000000000 : ℝ)^4185 ≤ (43825862167909/100000000000000 : ℝ)^3161 := by
    have hnat : (2681409091 : ℕ)^4185*100000000000000^3161 ≤ 43825862167909^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681409091 5000000000 43825862167909 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211262899/400000000 : ℝ)^4185 ≤ (42948986339799/100000000000000 : ℝ)^3161 := by
    have hnat : (211262899 : ℕ)^4185*100000000000000^3161 ≤ 42948986339799^3161*400000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211262899 400000000 42948986339799 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108479913/500000000 : ℝ)^4185 ≤ (529006059063/4000000000000 : ℝ)^3161 := by
    have hnat : (108479913 : ℕ)^4185*4000000000000^3161 ≤ 529006059063^3161*500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108479913 500000000 529006059063 4000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681409091/5000000000 : ℝ), (211262899/400000000 : ℝ), (-108479913/500000000 : ℝ)] ![(43825862167909/100000000000000 : ℝ), (42948986339799/100000000000000 : ℝ), (529006059063/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681409091/5000000000 : ℝ)|^4185 ≤ (43825862167909/100000000000000 : ℝ)^3161
        have hw : |(2681409091/5000000000 : ℝ)|=(2681409091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211262899/400000000 : ℝ)|^4185 ≤ (42948986339799/100000000000000 : ℝ)^3161
        have hw : |(211262899/400000000 : ℝ)|=(211262899/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108479913/500000000 : ℝ)|^4185 ≤ (529006059063/4000000000000 : ℝ)^3161
        have hw : |(-108479913/500000000 : ℝ)|=(108479913/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_7 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2126109463/5000000000 : ℝ)*x 0 + (883121197/2000000000 : ℝ)*x 1 + (220780299/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126109463/5000000000 : ℝ)^4185 ≤ (32233416806807/100000000000000 : ℝ)^3161 := by
    have hnat : (2126109463 : ℕ)^4185*100000000000000^3161 ≤ 32233416806807^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126109463 5000000000 32233416806807 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883121197/2000000000 : ℝ)^4185 ≤ (33883291617223/100000000000000 : ℝ)^3161 := by
    have hnat : (883121197 : ℕ)^4185*100000000000000^3161 ≤ 33883291617223^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883121197 2000000000 33883291617223 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220780299/500000000 : ℝ)^4185 ≤ (16941645783213/50000000000000 : ℝ)^3161 := by
    have hnat : (220780299 : ℕ)^4185*50000000000000^3161 ≤ 16941645783213^3161*500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220780299 500000000 16941645783213 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126109463/5000000000 : ℝ), (883121197/2000000000 : ℝ), (220780299/500000000 : ℝ)] ![(32233416806807/100000000000000 : ℝ), (33883291617223/100000000000000 : ℝ), (16941645783213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126109463/5000000000 : ℝ)|^4185 ≤ (32233416806807/100000000000000 : ℝ)^3161
        have hw : |(2126109463/5000000000 : ℝ)|=(2126109463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(883121197/2000000000 : ℝ)|^4185 ≤ (33883291617223/100000000000000 : ℝ)^3161
        have hw : |(883121197/2000000000 : ℝ)|=(883121197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220780299/500000000 : ℝ)|^4185 ≤ (16941645783213/50000000000000 : ℝ)^3161
        have hw : |(220780299/500000000 : ℝ)|=(220780299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_8 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2224474377/10000000000 : ℝ)*x 0 + (1304354849/2500000000 : ℝ)*x 1 + (1346353571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2224474377/10000000000 : ℝ)^4185 ≤ (1708728125929/12500000000000 : ℝ)^3161 := by
    have hnat : (2224474377 : ℕ)^4185*12500000000000^3161 ≤ 1708728125929^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224474377 10000000000 1708728125929 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304354849/2500000000 : ℝ)^4185 ≤ (42259666935259/100000000000000 : ℝ)^3161 := by
    have hnat : (1304354849 : ℕ)^4185*100000000000000^3161 ≤ 42259666935259^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304354849 2500000000 42259666935259 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346353571/2500000000 : ℝ)^4185 ≤ (11017627011241/25000000000000 : ℝ)^3161 := by
    have hnat : (1346353571 : ℕ)^4185*25000000000000^3161 ≤ 11017627011241^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346353571 2500000000 11017627011241 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2224474377/10000000000 : ℝ), (1304354849/2500000000 : ℝ), (1346353571/2500000000 : ℝ)] ![(1708728125929/12500000000000 : ℝ), (42259666935259/100000000000000 : ℝ), (11017627011241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2224474377/10000000000 : ℝ)|^4185 ≤ (1708728125929/12500000000000 : ℝ)^3161
        have hw : |(-2224474377/10000000000 : ℝ)|=(2224474377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304354849/2500000000 : ℝ)|^4185 ≤ (42259666935259/100000000000000 : ℝ)^3161
        have hw : |(1304354849/2500000000 : ℝ)|=(1304354849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346353571/2500000000 : ℝ)|^4185 ≤ (11017627011241/25000000000000 : ℝ)^3161
        have hw : |(1346353571/2500000000 : ℝ)|=(1346353571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_9 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132237719/250000000 : ℝ)*x 0 + (-1064284267/5000000000 : ℝ)*x 1 + (134635347/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132237719/250000000 : ℝ)^4185 ≤ (43034450405651/100000000000000 : ℝ)^3161 := by
    have hnat : (132237719 : ℕ)^4185*100000000000000^3161 ≤ 43034450405651^3161*250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132237719 250000000 43034450405651 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064284267/5000000000 : ℝ)^4185 ≤ (3223761478609/25000000000000 : ℝ)^3161 := by
    have hnat : (1064284267 : ℕ)^4185*25000000000000^3161 ≤ 3223761478609^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064284267 5000000000 3223761478609 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134635347/250000000 : ℝ)^4185 ≤ (11017625916979/25000000000000 : ℝ)^3161 := by
    have hnat : (134635347 : ℕ)^4185*25000000000000^3161 ≤ 11017625916979^3161*250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134635347 250000000 11017625916979 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132237719/250000000 : ℝ), (-1064284267/5000000000 : ℝ), (134635347/250000000 : ℝ)] ![(43034450405651/100000000000000 : ℝ), (3223761478609/25000000000000 : ℝ), (11017625916979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132237719/250000000 : ℝ)|^4185 ≤ (43034450405651/100000000000000 : ℝ)^3161
        have hw : |(132237719/250000000 : ℝ)|=(132237719/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1064284267/5000000000 : ℝ)|^4185 ≤ (3223761478609/25000000000000 : ℝ)^3161
        have hw : |(-1064284267/5000000000 : ℝ)|=(1064284267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134635347/250000000 : ℝ)|^4185 ≤ (11017625916979/25000000000000 : ℝ)^3161
        have hw : |(134635347/250000000 : ℝ)|=(134635347/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_10 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644754307/5000000000 : ℝ)*x 0 + (107708271/200000000 : ℝ)*x 1 + (-85142767/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644754307/5000000000 : ℝ)^4185 ≤ (43034448833027/100000000000000 : ℝ)^3161 := by
    have hnat : (2644754307 : ℕ)^4185*100000000000000^3161 ≤ 43034448833027^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644754307 5000000000 43034448833027 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107708271/200000000 : ℝ)^4185 ≤ (8814100018521/20000000000000 : ℝ)^3161 := by
    have hnat : (107708271 : ℕ)^4185*20000000000000^3161 ≤ 8814100018521^3161*200000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107708271 200000000 8814100018521 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85142767/400000000 : ℝ)^4185 ≤ (12895051055633/100000000000000 : ℝ)^3161 := by
    have hnat : (85142767 : ℕ)^4185*100000000000000^3161 ≤ 12895051055633^3161*400000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85142767 400000000 12895051055633 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644754307/5000000000 : ℝ), (107708271/200000000 : ℝ), (-85142767/400000000 : ℝ)] ![(43034448833027/100000000000000 : ℝ), (8814100018521/20000000000000 : ℝ), (12895051055633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644754307/5000000000 : ℝ)|^4185 ≤ (43034448833027/100000000000000 : ℝ)^3161
        have hw : |(2644754307/5000000000 : ℝ)|=(2644754307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107708271/200000000 : ℝ)|^4185 ≤ (8814100018521/20000000000000 : ℝ)^3161
        have hw : |(107708271/200000000 : ℝ)|=(107708271/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85142767/400000000 : ℝ)|^4185 ≤ (12895051055633/100000000000000 : ℝ)^3161
        have hw : |(-85142767/400000000 : ℝ)|=(85142767/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_11 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4488567949/10000000000 : ℝ)*x 0 + (4297311503/10000000000 : ℝ)*x 1 + (1074327881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4488567949/10000000000 : ℝ)^4185 ≤ (34626514838707/100000000000000 : ℝ)^3161 := by
    have hnat : (4488567949 : ℕ)^4185*100000000000000^3161 ≤ 34626514838707^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488567949 10000000000 34626514838707 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4297311503/10000000000 : ℝ)^4185 ≤ (6537348493797/20000000000000 : ℝ)^3161 := by
    have hnat : (4297311503 : ℕ)^4185*20000000000000^3161 ≤ 6537348493797^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297311503 10000000000 6537348493797 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074327881/2500000000 : ℝ)^4185 ≤ (32686742680463/100000000000000 : ℝ)^3161 := by
    have hnat : (1074327881 : ℕ)^4185*100000000000000^3161 ≤ 32686742680463^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074327881 2500000000 32686742680463 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4488567949/10000000000 : ℝ), (4297311503/10000000000 : ℝ), (1074327881/2500000000 : ℝ)] ![(34626514838707/100000000000000 : ℝ), (6537348493797/20000000000000 : ℝ), (32686742680463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4488567949/10000000000 : ℝ)|^4185 ≤ (34626514838707/100000000000000 : ℝ)^3161
        have hw : |(4488567949/10000000000 : ℝ)|=(4488567949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4297311503/10000000000 : ℝ)|^4185 ≤ (6537348493797/20000000000000 : ℝ)^3161
        have hw : |(4297311503/10000000000 : ℝ)|=(4297311503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1074327881/2500000000 : ℝ)|^4185 ≤ (32686742680463/100000000000000 : ℝ)^3161
        have hw : |(1074327881/2500000000 : ℝ)|=(1074327881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_12 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-259716869/1250000000 : ℝ)*x 0 + (5438703443/10000000000 : ℝ)*x 1 + (5273519/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259716869/1250000000 : ℝ)^4185 ≤ (12488916380471/100000000000000 : ℝ)^3161 := by
    have hnat : (259716869 : ℕ)^4185*100000000000000^3161 ≤ 12488916380471^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259716869 1250000000 12488916380471 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438703443/10000000000 : ℝ)^4185 ≤ (44648780806429/100000000000000 : ℝ)^3161 := by
    have hnat : (5438703443 : ℕ)^4185*100000000000000^3161 ≤ 44648780806429^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438703443 10000000000 44648780806429 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273519/10000000 : ℝ)^4185 ≤ (42862302798991/100000000000000 : ℝ)^3161 := by
    have hnat : (5273519 : ℕ)^4185*100000000000000^3161 ≤ 42862302798991^3161*10000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273519 10000000 42862302798991 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259716869/1250000000 : ℝ), (5438703443/10000000000 : ℝ), (5273519/10000000 : ℝ)] ![(12488916380471/100000000000000 : ℝ), (44648780806429/100000000000000 : ℝ), (42862302798991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259716869/1250000000 : ℝ)|^4185 ≤ (12488916380471/100000000000000 : ℝ)^3161
        have hw : |(-259716869/1250000000 : ℝ)|=(259716869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438703443/10000000000 : ℝ)|^4185 ≤ (44648780806429/100000000000000 : ℝ)^3161
        have hw : |(5438703443/10000000000 : ℝ)|=(5438703443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273519/10000000 : ℝ)|^4185 ≤ (42862302798991/100000000000000 : ℝ)^3161
        have hw : |(5273519/10000000 : ℝ)|=(5273519/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_13 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671062709/1250000000 : ℝ)*x 0 + (-2172717563/10000000000 : ℝ)*x 1 + (2636759527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671062709/1250000000 : ℝ)^4185 ≤ (21943682703497/50000000000000 : ℝ)^3161 := by
    have hnat : (671062709 : ℕ)^4185*50000000000000^3161 ≤ 21943682703497^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671062709 1250000000 21943682703497 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2172717563/10000000000 : ℝ)^4185 ≤ (3312582799957/25000000000000 : ℝ)^3161 := by
    have hnat : (2172717563 : ℕ)^4185*25000000000000^3161 ≤ 3312582799957^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172717563 10000000000 3312582799957 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636759527/5000000000 : ℝ)^4185 ≤ (10715575845019/25000000000000 : ℝ)^3161 := by
    have hnat : (2636759527 : ℕ)^4185*25000000000000^3161 ≤ 10715575845019^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636759527 5000000000 10715575845019 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671062709/1250000000 : ℝ), (-2172717563/10000000000 : ℝ), (2636759527/5000000000 : ℝ)] ![(21943682703497/50000000000000 : ℝ), (3312582799957/25000000000000 : ℝ), (10715575845019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671062709/1250000000 : ℝ)|^4185 ≤ (21943682703497/50000000000000 : ℝ)^3161
        have hw : |(671062709/1250000000 : ℝ)|=(671062709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2172717563/10000000000 : ℝ)|^4185 ≤ (3312582799957/25000000000000 : ℝ)^3161
        have hw : |(-2172717563/10000000000 : ℝ)|=(2172717563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636759527/5000000000 : ℝ)|^4185 ≤ (10715575845019/25000000000000 : ℝ)^3161
        have hw : |(2636759527/5000000000 : ℝ)|=(2636759527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_14 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368501773/10000000000 : ℝ)*x 0 + (1054703727/2000000000 : ℝ)*x 1 + (-1086358993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368501773/10000000000 : ℝ)^4185 ≤ (21943683250071/50000000000000 : ℝ)^3161 := by
    have hnat : (5368501773 : ℕ)^4185*50000000000000^3161 ≤ 21943683250071^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368501773 10000000000 21943683250071 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054703727/2000000000 : ℝ)^4185 ≤ (21431149435643/50000000000000 : ℝ)^3161 := by
    have hnat : (1054703727 : ℕ)^4185*50000000000000^3161 ≤ 21431149435643^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054703727 2000000000 21431149435643 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086358993/5000000000 : ℝ)^4185 ≤ (530013384607/4000000000000 : ℝ)^3161 := by
    have hnat : (1086358993 : ℕ)^4185*4000000000000^3161 ≤ 530013384607^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086358993 5000000000 530013384607 4000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368501773/10000000000 : ℝ), (1054703727/2000000000 : ℝ), (-1086358993/5000000000 : ℝ)] ![(21943683250071/50000000000000 : ℝ), (21431149435643/50000000000000 : ℝ), (530013384607/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368501773/10000000000 : ℝ)|^4185 ≤ (21943683250071/50000000000000 : ℝ)^3161
        have hw : |(5368501773/10000000000 : ℝ)|=(5368501773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054703727/2000000000 : ℝ)|^4185 ≤ (21431149435643/50000000000000 : ℝ)^3161
        have hw : |(1054703727/2000000000 : ℝ)|=(1054703727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1086358993/5000000000 : ℝ)|^4185 ≤ (530013384607/4000000000000 : ℝ)^3161
        have hw : |(-1086358993/5000000000 : ℝ)|=(1086358993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_box_15 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (423363561/1000000000 : ℝ)*x 0 + (884955101/2000000000 : ℝ)*x 1 + (4424775003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423363561/1000000000 : ℝ)^4185 ≤ (4005880793723/12500000000000 : ℝ)^3161 := by
    have hnat : (423363561 : ℕ)^4185*12500000000000^3161 ≤ 4005880793723^3161*1000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423363561 1000000000 4005880793723 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884955101/2000000000 : ℝ)^4185 ≤ (33976479369049/100000000000000 : ℝ)^3161 := by
    have hnat : (884955101 : ℕ)^4185*100000000000000^3161 ≤ 33976479369049^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884955101 2000000000 33976479369049 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4424775003/10000000000 : ℝ)^4185 ≤ (33976474265623/100000000000000 : ℝ)^3161 := by
    have hnat : (4424775003 : ℕ)^4185*100000000000000^3161 ≤ 33976474265623^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4424775003 10000000000 33976474265623 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423363561/1000000000 : ℝ), (884955101/2000000000 : ℝ), (4424775003/10000000000 : ℝ)] ![(4005880793723/12500000000000 : ℝ), (33976479369049/100000000000000 : ℝ), (33976474265623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423363561/1000000000 : ℝ)|^4185 ≤ (4005880793723/12500000000000 : ℝ)^3161
        have hw : |(423363561/1000000000 : ℝ)|=(423363561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884955101/2000000000 : ℝ)|^4185 ≤ (33976479369049/100000000000000 : ℝ)^3161
        have hw : |(884955101/2000000000 : ℝ)|=(884955101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4424775003/10000000000 : ℝ)|^4185 ≤ (33976474265623/100000000000000 : ℝ)^3161
        have hw : |(4424775003/10000000000 : ℝ)|=(4424775003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1177_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15559/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29663/50000 : ℝ) ∧ (15983/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41601/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11399/100000 : ℝ) ^ (8369/2048 : ℝ) ≤ (13994454904180333/100000000000000000000 : ℝ) := by
    have hpowers : (11399/100000 : ℝ)^8369 ≤ (13994454904180333/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11399 : ℕ)^8369*100000000000000000000^2048 ≤ 13994454904180333^2048*100000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11399 100000 13994454904180333 100000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11399/100000 : ℝ)) (X := (13994454904180333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3517/25000 : ℝ) ^ (8369/2048 : ℝ) ≤ (6612181261326821/20000000000000000000 : ℝ) := by
    have hpowers : (3517/25000 : ℝ)^8369 ≤ (6612181261326821/20000000000000000000 : ℝ)^2048 := by
      have hnat : (3517 : ℕ)^8369*20000000000000000000^2048 ≤ 6612181261326821^2048*25000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3517 25000 6612181261326821 20000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3517/25000 : ℝ)) (X := (6612181261326821/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013994454904180333/50000000000000000000 : ℝ) ≤ (5000342425794683/5000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (50013994454904180333/50000000000000000000 : ℝ)^2048 ≤ (5000342425794683/5000000000000000 : ℝ)^8369 := by
      have hnat : (50013994454904180333 : ℕ)^2048*5000000000000000^8369 ≤ 5000342425794683^8369*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013994454904180333 50000000000000000000 5000342425794683 5000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000342425794683/5000000000000000 : ℝ)) (X := (50013994454904180333/50000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023527680605407219/50000000000000000000 : ℝ) ≤ (31253597811099/31250000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (50023527680605407219/50000000000000000000 : ℝ)^2048 ≤ (31253597811099/31250000000000 : ℝ)^8369 := by
      have hnat : (50023527680605407219 : ℕ)^2048*31250000000000^8369 ≤ 31253597811099^8369*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023527680605407219 50000000000000000000 31253597811099 31250000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31253597811099/31250000000000 : ℝ)) (X := (50023527680605407219/50000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006612181261326821/10000000000000000000 : ℝ) ≤ (5000808873756997/5000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (10006612181261326821/10000000000000000000 : ℝ)^2048 ≤ (5000808873756997/5000000000000000 : ℝ)^8369 := by
      have hnat : (10006612181261326821 : ℕ)^2048*5000000000000000^8369 ≤ 5000808873756997^8369*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006612181261326821 10000000000000000000 5000808873756997 5000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000808873756997/5000000000000000 : ℝ)) (X := (10006612181261326821/10000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13994454904180333/100000000000000000000 : ℝ) ≤ ((13340596894123591641/13345000000000000000 : ℝ)+2*(233223981157/133450000000000 : ℝ)*(11399/100000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (13340596894123591641/13345000000000000000 : ℝ)+2*(233223981157/133450000000000 : ℝ)*(11399/100000 : ℝ)=(5000342425794683/5000000000000000 : ℝ) by norm_num, show 1+2*(13994454904180333/100000000000000000000 : ℝ)=(50013994454904180333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6612181261326821/20000000000000000000 : ℝ)+(13994454904180333/100000000000000000000 : ℝ) ≤ ((13340596894123591641/13345000000000000000 : ℝ)+(233223981157/133450000000000 : ℝ)*((3517/25000 : ℝ)+(11399/100000 : ℝ)))^(8369/2048 : ℝ) := by
    rw [show (13340596894123591641/13345000000000000000 : ℝ)+(233223981157/133450000000000 : ℝ)*((3517/25000 : ℝ)+(11399/100000 : ℝ))=(31253597811099/31250000000000 : ℝ) by norm_num, show 1+(6612181261326821/20000000000000000000 : ℝ)+(13994454904180333/100000000000000000000 : ℝ)=(50023527680605407219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6612181261326821/20000000000000000000 : ℝ) ≤ ((13340596894123591641/13345000000000000000 : ℝ)+2*(233223981157/133450000000000 : ℝ)*(3517/25000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (13340596894123591641/13345000000000000000 : ℝ)+2*(233223981157/133450000000000 : ℝ)*(3517/25000 : ℝ)=(5000808873756997/5000000000000000 : ℝ) by norm_num, show 1+2*(6612181261326821/20000000000000000000 : ℝ)=(10006612181261326821/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13340596894123591641/13345000000000000000 : ℝ)*(X 1 0+X 2 0)+(233223981157/133450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (13340596894123591641/13345000000000000000 : ℝ)) (alpha := (233223981157/133450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13340596894123591641/13345000000000000000 : ℝ)*(X 0 1+X 2 1)+(233223981157/133450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (13340596894123591641/13345000000000000000 : ℝ)) (alpha := (233223981157/133450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13340596894123591641/13345000000000000000 : ℝ)*(X 0 2+X 1 2)+(233223981157/133450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (13340596894123591641/13345000000000000000 : ℝ)) (alpha := (233223981157/133450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2024517699/10000000000 : ℝ)*X 0 0+(5375804509/10000000000 : ℝ)*X 0 1+(2687901077/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((662036871/1250000000 : ℝ)*X 1 0+(-1066214621/5000000000 : ℝ)*X 1 1+(5375803967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296295843/10000000000 : ℝ)*X 2 0+(1075160557/2000000000 : ℝ)*X 2 1+(-2132429661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4466942241/10000000000 : ℝ)*X 0 0+(4308264383/10000000000 : ℝ)*X 0 1+(4308265393/10000000000 : ℝ)*X 0 2+(4466942241/10000000000 : ℝ)*X 1 0+(4308264383/10000000000 : ℝ)*X 1 1+(4308265393/10000000000 : ℝ)*X 1 2+(4466942241/10000000000 : ℝ)*X 2 0+(4308264383/10000000000 : ℝ)*X 2 1+(4308265393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-455478841/2000000000 : ℝ)*X 0 0+(5281572251/10000000000 : ℝ)*X 0 1+(2640786383/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1340704601/2500000000 : ℝ)*X 1 0+(-2169598029/10000000000 : ℝ)*X 1 1+(211262897/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681409091/5000000000 : ℝ)*X 2 0+(211262899/400000000 : ℝ)*X 2 1+(-108479913/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2126109463/5000000000 : ℝ)*X 0 0+(883121197/2000000000 : ℝ)*X 0 1+(220780299/500000000 : ℝ)*X 0 2+(2126109463/5000000000 : ℝ)*X 1 0+(883121197/2000000000 : ℝ)*X 1 1+(220780299/500000000 : ℝ)*X 1 2+(2126109463/5000000000 : ℝ)*X 2 0+(883121197/2000000000 : ℝ)*X 2 1+(220780299/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2224474377/10000000000 : ℝ)*X 0 0+(1304354849/2500000000 : ℝ)*X 0 1+(1346353571/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((132237719/250000000 : ℝ)*X 1 0+(-1064284267/5000000000 : ℝ)*X 1 1+(134635347/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644754307/5000000000 : ℝ)*X 2 0+(107708271/200000000 : ℝ)*X 2 1+(-85142767/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4488567949/10000000000 : ℝ)*X 0 0+(4297311503/10000000000 : ℝ)*X 0 1+(1074327881/2500000000 : ℝ)*X 0 2+(4488567949/10000000000 : ℝ)*X 1 0+(4297311503/10000000000 : ℝ)*X 1 1+(1074327881/2500000000 : ℝ)*X 1 2+(4488567949/10000000000 : ℝ)*X 2 0+(4297311503/10000000000 : ℝ)*X 2 1+(1074327881/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-259716869/1250000000 : ℝ)*X 0 0+(5438703443/10000000000 : ℝ)*X 0 1+(5273519/10000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((671062709/1250000000 : ℝ)*X 1 0+(-2172717563/10000000000 : ℝ)*X 1 1+(2636759527/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368501773/10000000000 : ℝ)*X 2 0+(1054703727/2000000000 : ℝ)*X 2 1+(-1086358993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((423363561/1000000000 : ℝ)*X 0 0+(884955101/2000000000 : ℝ)*X 0 1+(4424775003/10000000000 : ℝ)*X 0 2+(423363561/1000000000 : ℝ)*X 1 0+(884955101/2000000000 : ℝ)*X 1 1+(4424775003/10000000000 : ℝ)*X 1 2+(423363561/1000000000 : ℝ)*X 2 0+(884955101/2000000000 : ℝ)*X 2 1+(4424775003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15559/25000 : ℝ) ≤ (-51906314280493003790563197/83406250000000000000000000 : ℝ) := by norm_num
    linear_combination (58663841/100000000000000 : ℝ)*(lower0) + (16042633/50000000000000 : ℝ)*(upper1) + (88033921/50000000000000 : ℝ)*(lower4) + (78995406963561/2000000000000 : ℝ)*(major0) + (78995406963561/2000000000000 : ℝ)*(major1) + (78995406963561/2000000000000 : ℝ)*(major2) + (14231114223/100000000000000 : ℝ)*(sp1) + (180042001/781250000000 : ℝ)*(sp2) + (7243596709/100000000000000 : ℝ)*(sp3) + (5289841407261877/100000000000000 : ℝ)*(sp4) + (1322461200964153/25000000000000 : ℝ)*(sp5) + (5289835989594707/100000000000000 : ℝ)*(sp6) + (2630418792173151/100000000000000 : ℝ)*(sp7) + (8813854479/50000000000000 : ℝ)*(sp12) + (131521301788493/5000000000000 : ℝ)*(f.failure) + (1057971806994167/20000000000000 : ℝ)*(f.sum) + (7139398621227/1334500000000000000000000000 : ℝ)*base65 + (146488855383176399/26690000000000000000000000000000 : ℝ)*base68 + (5266838869583601/26690000000000000000000000000000 : ℝ)*base69 + (318575960470063601/26690000000000000000000000000000 : ℝ)*base71 + (36676738651863/667250000000000000000000000 : ℝ)*base74 + (254966078106126399/26690000000000000000000000000000 : ℝ)*base76 + (124017031142523601/26690000000000000000000000000000 : ℝ)*base77 + (937630867028136399/26690000000000000000000000000000 : ℝ)*base80 + (1972408250901/2669000000000000000000000000 : ℝ)*base82 + (1433203/250000000000000000000 : ℝ)*base90 + (1433203/250000000000000000000 : ℝ)*base92 + (1433203/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29663/50000 : ℝ) ≤ (49483438196264374430439922300587/83406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (470540081/50000000000000 : ℝ)*(upper0) + (177292767/20000000000000 : ℝ)*(upper3) + (113064859/25000000000000 : ℝ)*(upper4) + (501807310608877/12500000000000 : ℝ)*(major0) + (501807310608877/12500000000000 : ℝ)*(major1) + (501807310608877/12500000000000 : ℝ)*(major2) + (5335632225595827/100000000000000 : ℝ)*(sp0) + (1333906549629993/25000000000000 : ℝ)*(sp1) + (5335628394424459/100000000000000 : ℝ)*(sp2) + (1336719047514689/50000000000000 : ℝ)*(sp3) + (4173581803/50000000000000 : ℝ)*(sp5) + (76890739/1250000000000 : ℝ)*(sp6) + (2320087751/100000000000000 : ℝ)*(sp8) + (68257812867/100000000000000 : ℝ)*(sp11) + (1336753176421123/50000000000000 : ℝ)*(f.failure) + (2667817272841789/50000000000000 : ℝ)*(f.sum) + (51647634138079/13345000000000000000000000000 : ℝ)*base65 + (1975534712251122157/166812500000000000000000000000000 : ℝ)*base67 + (2224387886750497157/166812500000000000000000000000000 : ℝ)*base69 + (3023232915569684657/166812500000000000000000000000000 : ℝ)*base71 + (431746044208459/13345000000000000000000000000 : ℝ)*base73 + (2502856862087497157/166812500000000000000000000000000 : ℝ)*base75 + (804353417186372157/166812500000000000000000000000000 : ℝ)*base77 + (6068873589879622157/166812500000000000000000000000000 : ℝ)*base79 + (95864589056289/13345000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (631933/2500000000000000000000 : ℝ)*base90 + (631933/2500000000000000000000 : ℝ)*base92 + (631933/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (15983/20000 : ℝ) ≤ (62735003291414287525584267/78500000000000000000000000 : ℝ) := by norm_num
    linear_combination (380943391/100000000000000 : ℝ)*(upper0) + (25345329/12500000000000 : ℝ)*(upper1) + (10087489/6250000000000 : ℝ)*(upper2) + (511088277/100000000000000 : ℝ)*(lower5) + (112051011971083/2500000000000 : ℝ)*(major0) + (112051011971083/2500000000000 : ℝ)*(major1) + (112051011971083/2500000000000 : ℝ)*(major2) + (10977078203/10000000000000 : ℝ)*(sp1) + (27518259643/100000000000000 : ℝ)*(sp3) + (2758217801/20000000000000 : ℝ)*(sp4) + (744065808086663/12500000000000 : ℝ)*(sp8) + (5952430485000279/100000000000000 : ℝ)*(sp9) + (5952540255782309/100000000000000 : ℝ)*(sp10) + (298487411642963/10000000000000 : ℝ)*(sp11) + (373112704336159/12500000000000 : ℝ)*(f.failure) + (5952540255782309/100000000000000 : ℝ)*(f.sum) + (5869796917/2453125000000000000000000 : ℝ)*base65 + (4679094912343659/1962500000000000000000000000000 : ℝ)*base67 + (13402259867143841/1962500000000000000000000000000 : ℝ)*base70 + (11635325086656159/1962500000000000000000000000000 : ℝ)*base71 + (6283482614253/157000000000000000000000000 : ℝ)*base74 + (30213021843993841/1962500000000000000000000000000 : ℝ)*base76 + (4810651568881159/1962500000000000000000000000000 : ℝ)*base77 + (72601726122993841/1962500000000000000000000000000 : ℝ)*base80 + (1129644971/490625000000000000000000 : ℝ)*base82 + (10769889/625000000000000000000 : ℝ)*base90 + (10769889/625000000000000000000 : ℝ)*base92 + (10769889/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-41601/50000 : ℝ) ≤ (-138787993136710642010098100211213/166812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52359629/20000000000000 : ℝ)*(lower0) + (3722009/100000000000000 : ℝ)*(lower1) + (210334959/100000000000000 : ℝ)*(lower4) + (1129304217246423/25000000000000 : ℝ)*(major0) + (1129304217246423/25000000000000 : ℝ)*(major1) + (1129304217246423/25000000000000 : ℝ)*(major2) + (1548004179/50000000000000 : ℝ)*(sp4) + (238826767251/50000000000000 : ℝ)*(sp6) + (90682445611/100000000000000 : ℝ)*(sp7) + (2366075509/100000000000000 : ℝ)*(sp8) + (3026916787543361/50000000000000 : ℝ)*(sp12) + (6053839037170589/100000000000000 : ℝ)*(sp13) + (6053361383636087/100000000000000 : ℝ)*(sp14) + (1504118675158527/50000000000000 : ℝ)*(sp15) + (376041004095333/12500000000000 : ℝ)*(f.failure) + (6053839037170589/100000000000000 : ℝ)*(f.sum) + (108325907854867/13345000000000000000000000000 : ℝ)*base66 + (903529742131074857/333625000000000000000000000000000 : ℝ)*base68 + (1644426577775699857/333625000000000000000000000000000 : ℝ)*base70 + (908292959969699857/333625000000000000000000000000000 : ℝ)*base72 + (43277893819761/6672500000000000000000000000 : ℝ)*base74 + (1682071495615449857/333625000000000000000000000000000 : ℝ)*base76 + (1889308200205074857/333625000000000000000000000000000 : ℝ)*base78 + (4766901712963949857/333625000000000000000000000000000 : ℝ)*base80 + (445909395141/417031250000000000000000000 : ℝ)*base82 + (2405157/625000000000000000000 : ℝ)*base89 + (2405157/625000000000000000000 : ℝ)*base91 + (2405157/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1177_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29663/50000 : ℝ) else (15983/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41601/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1177_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1177_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29663/50000 : ℝ) else (15983/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41601/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1177_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1177_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29663/50000 : ℝ) else (15983/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41601/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1177_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
