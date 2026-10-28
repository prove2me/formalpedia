-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1162_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:40:24.221442+00:00
-- url     : https://prove2.me/submissions/3ed4c0a6-feee-4a24-8536-e92dfe1a04ed

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
theorem support_rectangle_w1162_s0_0 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885496907/10000000000 : ℝ)*x 0 + (604971921/1000000000 : ℝ)*x 1 + (597874563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885496907/10000000000 : ℝ)^8355 ≤ (10968396374509/100000000000000 : ℝ)^6307 := by
    have hnat : (1885496907 : ℕ)^8355*100000000000000^6307 ≤ 10968396374509^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885496907 10000000000 10968396374509 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604971921/1000000000 : ℝ)^8355 ≤ (12846966728347/25000000000000 : ℝ)^6307 := by
    have hnat : (604971921 : ℕ)^8355*25000000000000^6307 ≤ 12846966728347^6307*1000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604971921 1000000000 12846966728347 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (597874563/1250000000 : ℝ)^8355 ≤ (37643736704973/100000000000000 : ℝ)^6307 := by
    have hnat : (597874563 : ℕ)^8355*100000000000000^6307 ≤ 37643736704973^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597874563 1250000000 37643736704973 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885496907/10000000000 : ℝ), (604971921/1000000000 : ℝ), (597874563/1250000000 : ℝ)] ![(10968396374509/100000000000000 : ℝ), (12846966728347/25000000000000 : ℝ), (37643736704973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885496907/10000000000 : ℝ)|^8355 ≤ (10968396374509/100000000000000 : ℝ)^6307
        have hw : |(-1885496907/10000000000 : ℝ)|=(1885496907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(604971921/1000000000 : ℝ)|^8355 ≤ (12846966728347/25000000000000 : ℝ)^6307
        have hw : |(604971921/1000000000 : ℝ)|=(604971921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(597874563/1250000000 : ℝ)|^8355 ≤ (37643736704973/100000000000000 : ℝ)^6307
        have hw : |(597874563/1250000000 : ℝ)|=(597874563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s0_1 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757833457/5000000000 : ℝ)*x 0 + (-2611881141/10000000000 : ℝ)*x 1 + (2391498249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757833457/5000000000 : ℝ)^8355 ≤ (1818654100743/4000000000000 : ℝ)^6307 := by
    have hnat : (2757833457 : ℕ)^8355*4000000000000^6307 ≤ 1818654100743^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757833457 5000000000 1818654100743 4000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611881141/10000000000 : ℝ)^8355 ≤ (8444955409679/50000000000000 : ℝ)^6307 := by
    have hnat : (2611881141 : ℕ)^8355*50000000000000^6307 ≤ 8444955409679^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611881141 10000000000 8444955409679 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2391498249/5000000000 : ℝ)^8355 ≤ (18821868321209/50000000000000 : ℝ)^6307 := by
    have hnat : (2391498249 : ℕ)^8355*50000000000000^6307 ≤ 18821868321209^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391498249 5000000000 18821868321209 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757833457/5000000000 : ℝ), (-2611881141/10000000000 : ℝ), (2391498249/5000000000 : ℝ)] ![(1818654100743/4000000000000 : ℝ), (8444955409679/50000000000000 : ℝ), (18821868321209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757833457/5000000000 : ℝ)|^8355 ≤ (1818654100743/4000000000000 : ℝ)^6307
        have hw : |(2757833457/5000000000 : ℝ)|=(2757833457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2611881141/10000000000 : ℝ)|^8355 ≤ (8444955409679/50000000000000 : ℝ)^6307
        have hw : |(-2611881141/10000000000 : ℝ)|=(2611881141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2391498249/5000000000 : ℝ)|^8355 ≤ (18821868321209/50000000000000 : ℝ)^6307
        have hw : |(2391498249/5000000000 : ℝ)|=(2391498249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s0_2 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757833457/5000000000 : ℝ)*x 0 + (597874563/1250000000 : ℝ)*x 1 + (-1305940567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757833457/5000000000 : ℝ)^8355 ≤ (1818654100743/4000000000000 : ℝ)^6307 := by
    have hnat : (2757833457 : ℕ)^8355*4000000000000^6307 ≤ 1818654100743^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757833457 5000000000 1818654100743 4000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597874563/1250000000 : ℝ)^8355 ≤ (37643736704973/100000000000000 : ℝ)^6307 := by
    have hnat : (597874563 : ℕ)^8355*100000000000000^6307 ≤ 37643736704973^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597874563 1250000000 37643736704973 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305940567/5000000000 : ℝ)^8355 ≤ (8444955379697/50000000000000 : ℝ)^6307 := by
    have hnat : (1305940567 : ℕ)^8355*50000000000000^6307 ≤ 8444955379697^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305940567 5000000000 8444955379697 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757833457/5000000000 : ℝ), (597874563/1250000000 : ℝ), (-1305940567/5000000000 : ℝ)] ![(1818654100743/4000000000000 : ℝ), (37643736704973/100000000000000 : ℝ), (8444955379697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757833457/5000000000 : ℝ)|^8355 ≤ (1818654100743/4000000000000 : ℝ)^6307
        have hw : |(2757833457/5000000000 : ℝ)|=(2757833457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597874563/1250000000 : ℝ)|^8355 ≤ (37643736704973/100000000000000 : ℝ)^6307
        have hw : |(597874563/1250000000 : ℝ)|=(597874563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1305940567/5000000000 : ℝ)|^8355 ≤ (8444955379697/50000000000000 : ℝ)^6307
        have hw : |(-1305940567/5000000000 : ℝ)|=(1305940567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s0_3 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (839875617/2000000000 : ℝ)*x 0 + (1560084981/5000000000 : ℝ)*x 1 + (88283937/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839875617/2000000000 : ℝ)^8355 ≤ (31682988774479/100000000000000 : ℝ)^6307 := by
    have hnat : (839875617 : ℕ)^8355*100000000000000^6307 ≤ 31682988774479^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839875617 2000000000 31682988774479 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560084981/5000000000 : ℝ)^8355 ≤ (21376103245601/100000000000000 : ℝ)^6307 := by
    have hnat : (1560084981 : ℕ)^8355*100000000000000^6307 ≤ 21376103245601^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560084981 5000000000 21376103245601 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88283937/156250000 : ℝ)^8355 ≤ (23470453981899/50000000000000 : ℝ)^6307 := by
    have hnat : (88283937 : ℕ)^8355*50000000000000^6307 ≤ 23470453981899^6307*156250000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88283937 156250000 23470453981899 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839875617/2000000000 : ℝ), (1560084981/5000000000 : ℝ), (88283937/156250000 : ℝ)] ![(31682988774479/100000000000000 : ℝ), (21376103245601/100000000000000 : ℝ), (23470453981899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839875617/2000000000 : ℝ)|^8355 ≤ (31682988774479/100000000000000 : ℝ)^6307
        have hw : |(839875617/2000000000 : ℝ)|=(839875617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560084981/5000000000 : ℝ)|^8355 ≤ (21376103245601/100000000000000 : ℝ)^6307
        have hw : |(1560084981/5000000000 : ℝ)|=(1560084981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(88283937/156250000 : ℝ)|^8355 ≤ (23470453981899/50000000000000 : ℝ)^6307
        have hw : |(88283937/156250000 : ℝ)|=(88283937/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s0_4 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-378116779/2000000000 : ℝ)*x 0 + (4815664127/10000000000 : ℝ)*x 1 + (46999231/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (378116779/2000000000 : ℝ)^8355 ≤ (1375951867781/12500000000000 : ℝ)^6307 := by
    have hnat : (378116779 : ℕ)^8355*12500000000000^6307 ≤ 1375951867781^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378116779 2000000000 1375951867781 12500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4815664127/10000000000 : ℝ)^8355 ≤ (37984705322899/100000000000000 : ℝ)^6307 := by
    have hnat : (4815664127 : ℕ)^8355*100000000000000^6307 ≤ 37984705322899^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815664127 10000000000 37984705322899 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46999231/78125000 : ℝ)^8355 ≤ (10201535943831/20000000000000 : ℝ)^6307 := by
    have hnat : (46999231 : ℕ)^8355*20000000000000^6307 ≤ 10201535943831^6307*78125000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46999231 78125000 10201535943831 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-378116779/2000000000 : ℝ), (4815664127/10000000000 : ℝ), (46999231/78125000 : ℝ)] ![(1375951867781/12500000000000 : ℝ), (37984705322899/100000000000000 : ℝ), (10201535943831/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-378116779/2000000000 : ℝ)|^8355 ≤ (1375951867781/12500000000000 : ℝ)^6307
        have hw : |(-378116779/2000000000 : ℝ)|=(378116779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4815664127/10000000000 : ℝ)|^8355 ≤ (37984705322899/100000000000000 : ℝ)^6307
        have hw : |(4815664127/10000000000 : ℝ)|=(4815664127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46999231/78125000 : ℝ)|^8355 ≤ (10201535943831/20000000000000 : ℝ)^6307
        have hw : |(46999231/78125000 : ℝ)|=(46999231/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s0_5 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (206854933/400000000 : ℝ)*x 0 + (-1378976231/10000000000 : ℝ)*x 1 + (3007950681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206854933/400000000 : ℝ)^8355 ≤ (2609086175583/6250000000000 : ℝ)^6307 := by
    have hnat : (206854933 : ℕ)^8355*6250000000000^6307 ≤ 2609086175583^6307*400000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206854933 400000000 2609086175583 6250000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378976231/10000000000 : ℝ)^8355 ≤ (7246943768241/100000000000000 : ℝ)^6307 := by
    have hnat : (1378976231 : ℕ)^8355*100000000000000^6307 ≤ 7246943768241^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378976231 10000000000 7246943768241 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3007950681/5000000000 : ℝ)^8355 ≤ (12751919351339/25000000000000 : ℝ)^6307 := by
    have hnat : (3007950681 : ℕ)^8355*25000000000000^6307 ≤ 12751919351339^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3007950681 5000000000 12751919351339 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206854933/400000000 : ℝ), (-1378976231/10000000000 : ℝ), (3007950681/5000000000 : ℝ)] ![(2609086175583/6250000000000 : ℝ), (7246943768241/100000000000000 : ℝ), (12751919351339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206854933/400000000 : ℝ)|^8355 ≤ (2609086175583/6250000000000 : ℝ)^6307
        have hw : |(206854933/400000000 : ℝ)|=(206854933/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1378976231/10000000000 : ℝ)|^8355 ≤ (7246943768241/100000000000000 : ℝ)^6307
        have hw : |(-1378976231/10000000000 : ℝ)|=(1378976231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3007950681/5000000000 : ℝ)|^8355 ≤ (12751919351339/25000000000000 : ℝ)^6307
        have hw : |(3007950681/5000000000 : ℝ)|=(3007950681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s0_6 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171373297/10000000000 : ℝ)*x 0 + (3007950721/5000000000 : ℝ)*x 1 + (-275795229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171373297/10000000000 : ℝ)^8355 ≤ (8349075701981/20000000000000 : ℝ)^6307 := by
    have hnat : (5171373297 : ℕ)^8355*20000000000000^6307 ≤ 8349075701981^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171373297 10000000000 8349075701981 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3007950721/5000000000 : ℝ)^8355 ≤ (51007678303919/100000000000000 : ℝ)^6307 := by
    have hnat : (3007950721 : ℕ)^8355*100000000000000^6307 ≤ 51007678303919^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3007950721 5000000000 51007678303919 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275795229/2000000000 : ℝ)^8355 ≤ (3623471584763/50000000000000 : ℝ)^6307 := by
    have hnat : (275795229 : ℕ)^8355*50000000000000^6307 ≤ 3623471584763^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275795229 2000000000 3623471584763 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171373297/10000000000 : ℝ), (3007950721/5000000000 : ℝ), (-275795229/2000000000 : ℝ)] ![(8349075701981/20000000000000 : ℝ), (51007678303919/100000000000000 : ℝ), (3623471584763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171373297/10000000000 : ℝ)|^8355 ≤ (8349075701981/20000000000000 : ℝ)^6307
        have hw : |(5171373297/10000000000 : ℝ)|=(5171373297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3007950721/5000000000 : ℝ)|^8355 ≤ (51007678303919/100000000000000 : ℝ)^6307
        have hw : |(3007950721/5000000000 : ℝ)|=(3007950721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275795229/2000000000 : ℝ)|^8355 ≤ (3623471584763/50000000000000 : ℝ)^6307
        have hw : |(-275795229/2000000000 : ℝ)|=(275795229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s0_7 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2104769209/5000000000 : ℝ)*x 0 + (5584925249/10000000000 : ℝ)*x 1 + (3187713569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104769209/5000000000 : ℝ)^8355 ≤ (15892288480423/50000000000000 : ℝ)^6307 := by
    have hnat : (2104769209 : ℕ)^8355*50000000000000^6307 ≤ 15892288480423^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104769209 5000000000 15892288480423 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5584925249/10000000000 : ℝ)^8355 ≤ (462241789687/1000000000000 : ℝ)^6307 := by
    have hnat : (5584925249 : ℕ)^8355*1000000000000^6307 ≤ 462241789687^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5584925249 10000000000 462241789687 1000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3187713569/10000000000 : ℝ)^8355 ≤ (879649761921/4000000000000 : ℝ)^6307 := by
    have hnat : (3187713569 : ℕ)^8355*4000000000000^6307 ≤ 879649761921^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187713569 10000000000 879649761921 4000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2104769209/5000000000 : ℝ), (5584925249/10000000000 : ℝ), (3187713569/10000000000 : ℝ)] ![(15892288480423/50000000000000 : ℝ), (462241789687/1000000000000 : ℝ), (879649761921/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2104769209/5000000000 : ℝ)|^8355 ≤ (15892288480423/50000000000000 : ℝ)^6307
        have hw : |(2104769209/5000000000 : ℝ)|=(2104769209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5584925249/10000000000 : ℝ)|^8355 ≤ (462241789687/1000000000000 : ℝ)^6307
        have hw : |(5584925249/10000000000 : ℝ)|=(5584925249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3187713569/10000000000 : ℝ)|^8355 ≤ (879649761921/4000000000000 : ℝ)^6307
        have hw : |(3187713569/10000000000 : ℝ)|=(3187713569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1162_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (31/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27739/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4177/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4177 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4177*1^1024 ≤ 0^1024*1^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4177/1024 : ℝ) ≤ (297626982900795597/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4177 ≤ (297626982900795597/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4177*12500000000000000000^1024 ≤ 297626982900795597^1024*5^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 297626982900795597 12500000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (297626982900795597/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4177 := by
      have hnat : (1 : ℕ)^1024*1^4177 ≤ 1^4177*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12797626982900795597/12500000000000000000 : ℝ) ≤ (5028926860238937/5000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (12797626982900795597/12500000000000000000 : ℝ)^1024 ≤ (5028926860238937/5000000000000000 : ℝ)^4177 := by
      have hnat : (12797626982900795597 : ℕ)^1024*5000000000000000^4177 ≤ 5028926860238937^4177*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12797626982900795597 12500000000000000000 5028926860238937 5000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028926860238937/5000000000000000 : ℝ)) (X := (12797626982900795597/12500000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6547626982900795597/6250000000000000000 : ℝ) ≤ (2528926860238937/2500000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (6547626982900795597/6250000000000000000 : ℝ)^1024 ≤ (2528926860238937/2500000000000000 : ℝ)^4177 := by
      have hnat : (6547626982900795597 : ℕ)^1024*2500000000000000^4177 ≤ 2528926860238937^4177*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6547626982900795597 6250000000000000000 2528926860238937 2500000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528926860238937/2500000000000000 : ℝ)) (X := (6547626982900795597/6250000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28926860238937/2000000000000000 : ℝ)*(0 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28926860238937/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(297626982900795597/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28926860238937/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4177/1024 : ℝ) := by
    rw [show (1 : ℝ)+(28926860238937/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028926860238937/5000000000000000 : ℝ) by norm_num, show 1+(297626982900795597/12500000000000000000 : ℝ)+(0 : ℝ)=(12797626982900795597/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(297626982900795597/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28926860238937/2000000000000000 : ℝ)*(2/5 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28926860238937/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528926860238937/2500000000000000 : ℝ) by norm_num, show 1+2*(297626982900795597/12500000000000000000 : ℝ)=(6547626982900795597/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28926860238937/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28926860238937/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28926860238937/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28926860238937/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28926860238937/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28926860238937/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1885496907/10000000000 : ℝ)*X 0 0+(604971921/1000000000 : ℝ)*X 0 1+(597874563/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2757833457/5000000000 : ℝ)*X 1 0+(-2611881141/10000000000 : ℝ)*X 1 1+(2391498249/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2757833457/5000000000 : ℝ)*X 2 0+(597874563/1250000000 : ℝ)*X 2 1+(-1305940567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((839875617/2000000000 : ℝ)*X 0 0+(1560084981/5000000000 : ℝ)*X 0 1+(88283937/156250000 : ℝ)*X 0 2+(839875617/2000000000 : ℝ)*X 1 0+(1560084981/5000000000 : ℝ)*X 1 1+(88283937/156250000 : ℝ)*X 1 2+(839875617/2000000000 : ℝ)*X 2 0+(1560084981/5000000000 : ℝ)*X 2 1+(88283937/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-378116779/2000000000 : ℝ)*X 0 0+(4815664127/10000000000 : ℝ)*X 0 1+(46999231/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((206854933/400000000 : ℝ)*X 1 0+(-1378976231/10000000000 : ℝ)*X 1 1+(3007950681/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5171373297/10000000000 : ℝ)*X 2 0+(3007950721/5000000000 : ℝ)*X 2 1+(-275795229/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2104769209/5000000000 : ℝ)*X 0 0+(5584925249/10000000000 : ℝ)*X 0 1+(3187713569/10000000000 : ℝ)*X 0 2+(2104769209/5000000000 : ℝ)*X 1 0+(5584925249/10000000000 : ℝ)*X 1 1+(3187713569/10000000000 : ℝ)*X 1 2+(2104769209/5000000000 : ℝ)*X 2 0+(5584925249/10000000000 : ℝ)*X 2 1+(3187713569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (406805004978722109/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (8456593/50000000000000 : ℝ)*(base1) + (100044127/25000000000000 : ℝ)*(base19) + (372087063/100000000000000 : ℝ)*(base23) + (5617889/20000000000000 : ℝ)*(base24) + (22980257/25000000000000 : ℝ)*(upper3) + (592349373480251/100000000000000 : ℝ)*(major0) + (592349373480251/100000000000000 : ℝ)*(major1) + (592349373480251/100000000000000 : ℝ)*(major2) + (394720049030053/50000000000000 : ℝ)*(sp0) + (98680069910737/12500000000000 : ℝ)*(sp1) + (98680069910737/12500000000000 : ℝ)*(sp2) + (197628507154279/50000000000000 : ℝ)*(sp3) + (219578871/25000000000000 : ℝ)*(sp4) + (351017841/50000000000000 : ℝ)*(sp7) + (395257733257427/100000000000000 : ℝ)*(f.failure) + (197360239865601/25000000000000 : ℝ)*(f.sum) + (242057092333187/100000000000000000000000000000 : ℝ)*base65 + (176736557666813/200000000000000000000000000000 : ℝ)*base68 + (948670796866813/200000000000000000000000000000 : ℝ)*base70 + (106912379266813/200000000000000000000000000000 : ℝ)*base72 + (237474882933187/100000000000000000000000000000 : ℝ)*base73 + (1023599571266813/200000000000000000000000000000 : ℝ)*base76 + (106912379266813/200000000000000000000000000000 : ℝ)*base78 + (139582328866813/200000000000000000000000000000 : ℝ)*base80 + (268394596933187/100000000000000000000000000000 : ℝ)*base81 + (33518507/5000000000000000000000 : ℝ)*base89 + (33518507/5000000000000000000000 : ℝ)*base91 + (33518507/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8411283003556496501769/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2480381/2500000000000 : ℝ)*(base1) + (2085370983/100000000000000 : ℝ)*(base19) + (2081225761/100000000000000 : ℝ)*(base23) + (114144149/50000000000000 : ℝ)*(upper3) + (245375483/100000000000000 : ℝ)*(upper5) + (6251600647221/1000000000000 : ℝ)*(major0) + (6251600647221/1000000000000 : ℝ)*(major1) + (6251600647221/1000000000000 : ℝ)*(major2) + (213193209/5000000000000 : ℝ)*(sp1) + (2134679813/50000000000000 : ℝ)*(sp2) + (833168582606467/100000000000000 : ℝ)*(sp4) + (166632426831213/20000000000000 : ℝ)*(sp5) + (833162132805841/100000000000000 : ℝ)*(sp6) + (417151266461627/100000000000000 : ℝ)*(sp7) + (417151365676867/100000000000000 : ℝ)*(f.failure) + (208292120847807/25000000000000 : ℝ)*(f.sum) + (186332076923/1000000000000000000000000000 : ℝ)*base66 + (335846180077/2000000000000000000000000000 : ℝ)*base67 + (23243991006077/2000000000000000000000000000 : ℝ)*base69 + (3713919582077/2000000000000000000000000000 : ℝ)*base71 + (1155094683923/1000000000000000000000000000 : ℝ)*base74 + (9865067178077/2000000000000000000000000000 : ℝ)*base75 + (8544048990077/2000000000000000000000000000 : ℝ)*base77 + (793275653923/2000000000000000000000000000 : ℝ)*base80 + (5020547110077/1000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (9204453/5000000000000000000000 : ℝ)*base90 + (9204453/5000000000000000000000 : ℝ)*base92 + (9204453/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1162_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (31/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27739/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1162_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1162_s1_0 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1044354323/5000000000 : ℝ)*x 0 + (45569621/80000000 : ℝ)*x 1 + (5006424411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044354323/5000000000 : ℝ)^8355 ≤ (6280577568987/50000000000000 : ℝ)^6307 := by
    have hnat : (1044354323 : ℕ)^8355*50000000000000^6307 ≤ 6280577568987^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044354323 5000000000 6280577568987 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45569621/80000000 : ℝ)^8355 ≤ (11862042871087/25000000000000 : ℝ)^6307 := by
    have hnat : (45569621 : ℕ)^8355*25000000000000^6307 ≤ 11862042871087^6307*80000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45569621 80000000 11862042871087 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5006424411/10000000000 : ℝ)^8355 ≤ (7998134674207/20000000000000 : ℝ)^6307 := by
    have hnat : (5006424411 : ℕ)^8355*20000000000000^6307 ≤ 7998134674207^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5006424411 10000000000 7998134674207 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1044354323/5000000000 : ℝ), (45569621/80000000 : ℝ), (5006424411/10000000000 : ℝ)] ![(6280577568987/50000000000000 : ℝ), (11862042871087/25000000000000 : ℝ), (7998134674207/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1044354323/5000000000 : ℝ)|^8355 ≤ (6280577568987/50000000000000 : ℝ)^6307
        have hw : |(-1044354323/5000000000 : ℝ)|=(1044354323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45569621/80000000 : ℝ)|^8355 ≤ (11862042871087/25000000000000 : ℝ)^6307
        have hw : |(45569621/80000000 : ℝ)|=(45569621/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5006424411/10000000000 : ℝ)|^8355 ≤ (7998134674207/20000000000000 : ℝ)^6307
        have hw : |(5006424411/10000000000 : ℝ)|=(5006424411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s1_1 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1083605521/2000000000 : ℝ)*x 0 + (-615143561/2500000000 : ℝ)*x 1 + (5006423463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083605521/2000000000 : ℝ)^8355 ≤ (5550403121939/12500000000000 : ℝ)^6307 := by
    have hnat : (1083605521 : ℕ)^8355*12500000000000^6307 ≤ 5550403121939^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083605521 2000000000 5550403121939 12500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615143561/2500000000 : ℝ)^8355 ≤ (3901527918613/25000000000000 : ℝ)^6307 := by
    have hnat : (615143561 : ℕ)^8355*25000000000000^6307 ≤ 3901527918613^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615143561 2500000000 3901527918613 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5006423463/10000000000 : ℝ)^8355 ≤ (39990663339601/100000000000000 : ℝ)^6307 := by
    have hnat : (5006423463 : ℕ)^8355*100000000000000^6307 ≤ 39990663339601^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5006423463 10000000000 39990663339601 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083605521/2000000000 : ℝ), (-615143561/2500000000 : ℝ), (5006423463/10000000000 : ℝ)] ![(5550403121939/12500000000000 : ℝ), (3901527918613/25000000000000 : ℝ), (39990663339601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083605521/2000000000 : ℝ)|^8355 ≤ (5550403121939/12500000000000 : ℝ)^6307
        have hw : |(1083605521/2000000000 : ℝ)|=(1083605521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-615143561/2500000000 : ℝ)|^8355 ≤ (3901527918613/25000000000000 : ℝ)^6307
        have hw : |(-615143561/2500000000 : ℝ)|=(615143561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5006423463/10000000000 : ℝ)|^8355 ≤ (39990663339601/100000000000000 : ℝ)^6307
        have hw : |(5006423463/10000000000 : ℝ)|=(5006423463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s1_2 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (338626857/625000000 : ℝ)*x 0 + (625802693/1250000000 : ℝ)*x 1 + (-2460573937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338626857/625000000 : ℝ)^8355 ≤ (11100811962633/25000000000000 : ℝ)^6307 := by
    have hnat : (338626857 : ℕ)^8355*25000000000000^6307 ≤ 11100811962633^6307*625000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338626857 625000000 11100811962633 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625802693/1250000000 : ℝ)^8355 ≤ (39990643033357/100000000000000 : ℝ)^6307 := by
    have hnat : (625802693 : ℕ)^8355*100000000000000^6307 ≤ 39990643033357^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625802693 1250000000 39990643033357 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2460573937/10000000000 : ℝ)^8355 ≤ (15606109095043/100000000000000 : ℝ)^6307 := by
    have hnat : (2460573937 : ℕ)^8355*100000000000000^6307 ≤ 15606109095043^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2460573937 10000000000 15606109095043 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338626857/625000000 : ℝ), (625802693/1250000000 : ℝ), (-2460573937/10000000000 : ℝ)] ![(11100811962633/25000000000000 : ℝ), (39990643033357/100000000000000 : ℝ), (15606109095043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338626857/625000000 : ℝ)|^8355 ≤ (11100811962633/25000000000000 : ℝ)^6307
        have hw : |(338626857/625000000 : ℝ)|=(338626857/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625802693/1250000000 : ℝ)|^8355 ≤ (39990643033357/100000000000000 : ℝ)^6307
        have hw : |(625802693/1250000000 : ℝ)|=(625802693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2460573937/10000000000 : ℝ)|^8355 ≤ (15606109095043/100000000000000 : ℝ)^6307
        have hw : |(-2460573937/10000000000 : ℝ)|=(2460573937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s1_3 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (134866863/312500000 : ℝ)*x 0 + (1840386169/5000000000 : ℝ)*x 1 + (2529224609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134866863/312500000 : ℝ)^8355 ≤ (8212793471533/25000000000000 : ℝ)^6307 := by
    have hnat : (134866863 : ℕ)^8355*25000000000000^6307 ≤ 8212793471533^6307*312500000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134866863 312500000 8212793471533 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1840386169/5000000000 : ℝ)^8355 ≤ (532134323097/2000000000000 : ℝ)^6307 := by
    have hnat : (1840386169 : ℕ)^8355*2000000000000^6307 ≤ 532134323097^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840386169 5000000000 532134323097 2000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2529224609/5000000000 : ℝ)^8355 ≤ (8108421988157/20000000000000 : ℝ)^6307 := by
    have hnat : (2529224609 : ℕ)^8355*20000000000000^6307 ≤ 8108421988157^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2529224609 5000000000 8108421988157 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134866863/312500000 : ℝ), (1840386169/5000000000 : ℝ), (2529224609/5000000000 : ℝ)] ![(8212793471533/25000000000000 : ℝ), (532134323097/2000000000000 : ℝ), (8108421988157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134866863/312500000 : ℝ)|^8355 ≤ (8212793471533/25000000000000 : ℝ)^6307
        have hw : |(134866863/312500000 : ℝ)|=(134866863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1840386169/5000000000 : ℝ)|^8355 ≤ (532134323097/2000000000000 : ℝ)^6307
        have hw : |(1840386169/5000000000 : ℝ)|=(1840386169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2529224609/5000000000 : ℝ)|^8355 ≤ (8108421988157/20000000000000 : ℝ)^6307
        have hw : |(2529224609/5000000000 : ℝ)|=(2529224609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s1_4 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2089491699/10000000000 : ℝ)*x 0 + (626971401/1250000000 : ℝ)*x 1 + (5686668811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089491699/10000000000 : ℝ)^8355 ≤ (12567393821101/100000000000000 : ℝ)^6307 := by
    have hnat : (2089491699 : ℕ)^8355*100000000000000^6307 ≤ 12567393821101^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089491699 10000000000 12567393821101 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626971401/1250000000 : ℝ)^8355 ≤ (2505600510327/6250000000000 : ℝ)^6307 := by
    have hnat : (626971401 : ℕ)^8355*6250000000000^6307 ≤ 2505600510327^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626971401 1250000000 2505600510327 6250000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5686668811/10000000000 : ℝ)^8355 ≤ (47342997997601/100000000000000 : ℝ)^6307 := by
    have hnat : (5686668811 : ℕ)^8355*100000000000000^6307 ≤ 47342997997601^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5686668811 10000000000 47342997997601 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2089491699/10000000000 : ℝ), (626971401/1250000000 : ℝ), (5686668811/10000000000 : ℝ)] ![(12567393821101/100000000000000 : ℝ), (2505600510327/6250000000000 : ℝ), (47342997997601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2089491699/10000000000 : ℝ)|^8355 ≤ (12567393821101/100000000000000 : ℝ)^6307
        have hw : |(-2089491699/10000000000 : ℝ)|=(2089491699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(626971401/1250000000 : ℝ)|^8355 ≤ (2505600510327/6250000000000 : ℝ)^6307
        have hw : |(626971401/1250000000 : ℝ)|=(626971401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5686668811/10000000000 : ℝ)|^8355 ≤ (47342997997601/100000000000000 : ℝ)^6307
        have hw : |(5686668811/10000000000 : ℝ)|=(5686668811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s1_5 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1310251027/2500000000 : ℝ)*x 0 + (-1780325329/10000000000 : ℝ)*x 1 + (22213563/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310251027/2500000000 : ℝ)^8355 ≤ (21245804609209/50000000000000 : ℝ)^6307 := by
    have hnat : (1310251027 : ℕ)^8355*50000000000000^6307 ≤ 21245804609209^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310251027 2500000000 21245804609209 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1780325329/10000000000 : ℝ)^8355 ≤ (2033071237283/20000000000000 : ℝ)^6307 := by
    have hnat : (1780325329 : ℕ)^8355*20000000000000^6307 ≤ 2033071237283^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780325329 10000000000 2033071237283 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22213563/39062500 : ℝ)^8355 ≤ (47343034579559/100000000000000 : ℝ)^6307 := by
    have hnat : (22213563 : ℕ)^8355*100000000000000^6307 ≤ 47343034579559^6307*39062500^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22213563 39062500 47343034579559 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310251027/2500000000 : ℝ), (-1780325329/10000000000 : ℝ), (22213563/39062500 : ℝ)] ![(21245804609209/50000000000000 : ℝ), (2033071237283/20000000000000 : ℝ), (47343034579559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310251027/2500000000 : ℝ)|^8355 ≤ (21245804609209/50000000000000 : ℝ)^6307
        have hw : |(1310251027/2500000000 : ℝ)|=(1310251027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1780325329/10000000000 : ℝ)|^8355 ≤ (2033071237283/20000000000000 : ℝ)^6307
        have hw : |(-1780325329/10000000000 : ℝ)|=(1780325329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22213563/39062500 : ℝ)|^8355 ≤ (47343034579559/100000000000000 : ℝ)^6307
        have hw : |(22213563/39062500 : ℝ)|=(22213563/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s1_6 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5241003157/10000000000 : ℝ)*x 0 + (5686673593/10000000000 : ℝ)*x 1 + (-356064909/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241003157/10000000000 : ℝ)^8355 ≤ (42491599004489/100000000000000 : ℝ)^6307 := by
    have hnat : (5241003157 : ℕ)^8355*100000000000000^6307 ≤ 42491599004489^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241003157 10000000000 42491599004489 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5686673593/10000000000 : ℝ)^8355 ≤ (23671525368251/50000000000000 : ℝ)^6307 := by
    have hnat : (5686673593 : ℕ)^8355*50000000000000^6307 ≤ 23671525368251^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5686673593 10000000000 23671525368251 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356064909/2000000000 : ℝ)^8355 ≤ (10165350256303/100000000000000 : ℝ)^6307 := by
    have hnat : (356064909 : ℕ)^8355*100000000000000^6307 ≤ 10165350256303^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356064909 2000000000 10165350256303 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241003157/10000000000 : ℝ), (5686673593/10000000000 : ℝ), (-356064909/2000000000 : ℝ)] ![(42491599004489/100000000000000 : ℝ), (23671525368251/50000000000000 : ℝ), (10165350256303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241003157/10000000000 : ℝ)|^8355 ≤ (42491599004489/100000000000000 : ℝ)^6307
        have hw : |(5241003157/10000000000 : ℝ)|=(5241003157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5686673593/10000000000 : ℝ)|^8355 ≤ (23671525368251/50000000000000 : ℝ)^6307
        have hw : |(5686673593/10000000000 : ℝ)|=(5686673593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-356064909/2000000000 : ℝ)|^8355 ≤ (10165350256303/100000000000000 : ℝ)^6307
        have hw : |(-356064909/2000000000 : ℝ)|=(356064909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s1_7 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4317291867/10000000000 : ℝ)*x 0 + (2519891597/5000000000 : ℝ)*x 1 + (3699805393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317291867/10000000000 : ℝ)^8355 ≤ (16433413605319/50000000000000 : ℝ)^6307 := by
    have hnat : (4317291867 : ℕ)^8355*50000000000000^6307 ≤ 16433413605319^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317291867 10000000000 16433413605319 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2519891597/5000000000 : ℝ)^8355 ≤ (40344046687631/100000000000000 : ℝ)^6307 := by
    have hnat : (2519891597 : ℕ)^8355*100000000000000^6307 ≤ 40344046687631^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519891597 5000000000 40344046687631 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3699805393/10000000000 : ℝ)^8355 ≤ (26789126087017/100000000000000 : ℝ)^6307 := by
    have hnat : (3699805393 : ℕ)^8355*100000000000000^6307 ≤ 26789126087017^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3699805393 10000000000 26789126087017 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317291867/10000000000 : ℝ), (2519891597/5000000000 : ℝ), (3699805393/10000000000 : ℝ)] ![(16433413605319/50000000000000 : ℝ), (40344046687631/100000000000000 : ℝ), (26789126087017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317291867/10000000000 : ℝ)|^8355 ≤ (16433413605319/50000000000000 : ℝ)^6307
        have hw : |(4317291867/10000000000 : ℝ)|=(4317291867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2519891597/5000000000 : ℝ)|^8355 ≤ (40344046687631/100000000000000 : ℝ)^6307
        have hw : |(2519891597/5000000000 : ℝ)|=(2519891597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3699805393/10000000000 : ℝ)|^8355 ≤ (26789126087017/100000000000000 : ℝ)^6307
        have hw : |(3699805393/10000000000 : ℝ)|=(3699805393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s1_8 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5523839/10000000000 : ℝ)*x 0 + (5490488649/10000000000 : ℝ)*x 1 + (1587715261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5523839/10000000000 : ℝ)^8355 ≤ (4834885381/100000000000000 : ℝ)^6307 := by
    have hnat : (5523839 : ℕ)^8355*100000000000000^6307 ≤ 4834885381^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523839 10000000000 4834885381 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490488649/10000000000 : ℝ)^8355 ≤ (1807664569437/4000000000000 : ℝ)^6307 := by
    have hnat : (5490488649 : ℕ)^8355*4000000000000^6307 ≤ 1807664569437^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490488649 10000000000 1807664569437 4000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1587715261/2500000000 : ℝ)^8355 ≤ (2740177543049/5000000000000 : ℝ)^6307 := by
    have hnat : (1587715261 : ℕ)^8355*5000000000000^6307 ≤ 2740177543049^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587715261 2500000000 2740177543049 5000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5523839/10000000000 : ℝ), (5490488649/10000000000 : ℝ), (1587715261/2500000000 : ℝ)] ![(4834885381/100000000000000 : ℝ), (1807664569437/4000000000000 : ℝ), (2740177543049/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5523839/10000000000 : ℝ)|^8355 ≤ (4834885381/100000000000000 : ℝ)^6307
        have hw : |(5523839/10000000000 : ℝ)|=(5523839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490488649/10000000000 : ℝ)|^8355 ≤ (1807664569437/4000000000000 : ℝ)^6307
        have hw : |(5490488649/10000000000 : ℝ)|=(5490488649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1587715261/2500000000 : ℝ)|^8355 ≤ (2740177543049/5000000000000 : ℝ)^6307
        have hw : |(1587715261/2500000000 : ℝ)|=(1587715261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s1_9 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (49199537/500000000 : ℝ)*x 0 + (-1099138673/2500000000 : ℝ)*x 1 + (6945046483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49199537/500000000 : ℝ)^8355 ≤ (231721590307/5000000000000 : ℝ)^6307 := by
    have hnat : (49199537 : ℕ)^8355*5000000000000^6307 ≤ 231721590307^6307*500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49199537 500000000 231721590307 5000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099138673/2500000000 : ℝ)^8355 ≤ (67337109771/200000000000 : ℝ)^6307 := by
    have hnat : (1099138673 : ℕ)^8355*200000000000^6307 ≤ 67337109771^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099138673 2500000000 67337109771 200000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6945046483/10000000000 : ℝ)^8355 ≤ (15424253322789/25000000000000 : ℝ)^6307 := by
    have hnat : (6945046483 : ℕ)^8355*25000000000000^6307 ≤ 15424253322789^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6945046483 10000000000 15424253322789 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(49199537/500000000 : ℝ), (-1099138673/2500000000 : ℝ), (6945046483/10000000000 : ℝ)] ![(231721590307/5000000000000 : ℝ), (67337109771/200000000000 : ℝ), (15424253322789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(49199537/500000000 : ℝ)|^8355 ≤ (231721590307/5000000000000 : ℝ)^6307
        have hw : |(49199537/500000000 : ℝ)|=(49199537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1099138673/2500000000 : ℝ)|^8355 ≤ (67337109771/200000000000 : ℝ)^6307
        have hw : |(-1099138673/2500000000 : ℝ)|=(1099138673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6945046483/10000000000 : ℝ)|^8355 ≤ (15424253322789/25000000000000 : ℝ)^6307
        have hw : |(6945046483/10000000000 : ℝ)|=(6945046483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s1_10 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (491991891/5000000000 : ℝ)*x 0 + (6945029643/10000000000 : ℝ)*x 1 + (-4396578507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491991891/5000000000 : ℝ)^8355 ≤ (579298549227/12500000000000 : ℝ)^6307 := by
    have hnat : (491991891 : ℕ)^8355*12500000000000^6307 ≤ 579298549227^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491991891 5000000000 579298549227 12500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6945029643/10000000000 : ℝ)^8355 ≤ (2467872604543/4000000000000 : ℝ)^6307 := by
    have hnat : (6945029643 : ℕ)^8355*4000000000000^6307 ≤ 2467872604543^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6945029643 10000000000 2467872604543 4000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4396578507/10000000000 : ℝ)^8355 ≤ (16834398239873/50000000000000 : ℝ)^6307 := by
    have hnat : (4396578507 : ℕ)^8355*50000000000000^6307 ≤ 16834398239873^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396578507 10000000000 16834398239873 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(491991891/5000000000 : ℝ), (6945029643/10000000000 : ℝ), (-4396578507/10000000000 : ℝ)] ![(579298549227/12500000000000 : ℝ), (2467872604543/4000000000000 : ℝ), (16834398239873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(491991891/5000000000 : ℝ)|^8355 ≤ (579298549227/12500000000000 : ℝ)^6307
        have hw : |(491991891/5000000000 : ℝ)|=(491991891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6945029643/10000000000 : ℝ)|^8355 ≤ (2467872604543/4000000000000 : ℝ)^6307
        have hw : |(6945029643/10000000000 : ℝ)|=(6945029643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4396578507/10000000000 : ℝ)|^8355 ≤ (16834398239873/50000000000000 : ℝ)^6307
        have hw : |(-4396578507/10000000000 : ℝ)|=(4396578507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s1_11 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (15308777/80000000 : ℝ)*x 0 + (2903552957/5000000000 : ℝ)*x 1 + (2510205191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15308777/80000000 : ℝ)^8355 ≤ (11185464832609/100000000000000 : ℝ)^6307 := by
    have hnat : (15308777 : ℕ)^8355*100000000000000^6307 ≤ 11185464832609^6307*80000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15308777 80000000 11185464832609 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2903552957/5000000000 : ℝ)^8355 ≤ (24337899801619/50000000000000 : ℝ)^6307 := by
    have hnat : (2903552957 : ℕ)^8355*50000000000000^6307 ≤ 24337899801619^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2903552957 5000000000 24337899801619 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510205191/5000000000 : ℝ)^8355 ≤ (40138735542281/100000000000000 : ℝ)^6307 := by
    have hnat : (2510205191 : ℕ)^8355*100000000000000^6307 ≤ 40138735542281^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510205191 5000000000 40138735542281 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(15308777/80000000 : ℝ), (2903552957/5000000000 : ℝ), (2510205191/5000000000 : ℝ)] ![(11185464832609/100000000000000 : ℝ), (24337899801619/50000000000000 : ℝ), (40138735542281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(15308777/80000000 : ℝ)|^8355 ≤ (11185464832609/100000000000000 : ℝ)^6307
        have hw : |(15308777/80000000 : ℝ)|=(15308777/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2903552957/5000000000 : ℝ)|^8355 ≤ (24337899801619/50000000000000 : ℝ)^6307
        have hw : |(2903552957/5000000000 : ℝ)|=(2903552957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510205191/5000000000 : ℝ)|^8355 ≤ (40138735542281/100000000000000 : ℝ)^6307
        have hw : |(2510205191/5000000000 : ℝ)|=(2510205191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1162_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (31/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5761/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20347/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27739/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (31/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27739/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (31/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27739/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (31/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27739/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (31/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27739/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (31/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27739/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (31/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (31/6250 : ℝ) ^ (4177/1024 : ℝ) ≤ (9944334273/25000000000000000000 : ℝ) := by
    have hpowers : (31/6250 : ℝ)^4177 ≤ (9944334273/25000000000000000000 : ℝ)^1024 := by
      have hnat : (31 : ℕ)^4177*25000000000000000000^1024 ≤ 9944334273^1024*6250^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31 6250 9944334273 25000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31/6250 : ℝ)) (X := (9944334273/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27739/100000 : ℝ) ^ (4177/1024 : ℝ) ≤ (33434191970993489/6250000000000000000 : ℝ) := by
    have hpowers : (27739/100000 : ℝ)^4177 ≤ (33434191970993489/6250000000000000000 : ℝ)^1024 := by
      have hnat : (27739 : ℕ)^4177*6250000000000000000^1024 ≤ 33434191970993489^1024*100000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27739 100000 33434191970993489 6250000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27739/100000 : ℝ)) (X := (33434191970993489/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000009944334273/12500000000000000000 : ℝ) ≤ (10000000001950299/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (12500000009944334273/12500000000000000000 : ℝ)^1024 ≤ (10000000001950299/10000000000000000 : ℝ)^4177 := by
      have hnat : (12500000009944334273 : ℕ)^1024*10000000000000000^4177 ≤ 10000000001950299^4177*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000009944334273 12500000000000000000 10000000001950299 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000001950299/10000000000000000 : ℝ)) (X := (12500000009944334273/12500000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25133736777828308229/25000000000000000000 : ℝ) ≤ (10013087941111883/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (25133736777828308229/25000000000000000000 : ℝ)^1024 ≤ (10013087941111883/10000000000000000 : ℝ)^4177 := by
      have hnat : (25133736777828308229 : ℕ)^1024*10000000000000000^4177 ≤ 10013087941111883^4177*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25133736777828308229 25000000000000000000 10013087941111883 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013087941111883/10000000000000000 : ℝ)) (X := (25133736777828308229/25000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3158434191970993489/3125000000000000000 : ℝ) ≤ (10026175880273467/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (3158434191970993489/3125000000000000000 : ℝ)^1024 ≤ (10026175880273467/10000000000000000 : ℝ)^4177 := by
      have hnat : (3158434191970993489 : ℕ)^1024*10000000000000000^4177 ≤ 10026175880273467^4177*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3158434191970993489 3125000000000000000 10026175880273467 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026175880273467/10000000000000000 : ℝ)) (X := (3158434191970993489/3125000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9944334273/25000000000000000000 : ℝ) ≤ ((272417016817483704329/272430000000000000000 : ℝ)+2*(817996197599/170268750000000 : ℝ)*(31/6250 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (272417016817483704329/272430000000000000000 : ℝ)+2*(817996197599/170268750000000 : ℝ)*(31/6250 : ℝ)=(10000000001950299/10000000000000000 : ℝ) by norm_num, show 1+2*(9944334273/25000000000000000000 : ℝ)=(12500000009944334273/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33434191970993489/6250000000000000000 : ℝ)+(9944334273/25000000000000000000 : ℝ) ≤ ((272417016817483704329/272430000000000000000 : ℝ)+(817996197599/170268750000000 : ℝ)*((27739/100000 : ℝ)+(31/6250 : ℝ)))^(4177/1024 : ℝ) := by
    rw [show (272417016817483704329/272430000000000000000 : ℝ)+(817996197599/170268750000000 : ℝ)*((27739/100000 : ℝ)+(31/6250 : ℝ))=(10013087941111883/10000000000000000 : ℝ) by norm_num, show 1+(33434191970993489/6250000000000000000 : ℝ)+(9944334273/25000000000000000000 : ℝ)=(25133736777828308229/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33434191970993489/6250000000000000000 : ℝ) ≤ ((272417016817483704329/272430000000000000000 : ℝ)+2*(817996197599/170268750000000 : ℝ)*(27739/100000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (272417016817483704329/272430000000000000000 : ℝ)+2*(817996197599/170268750000000 : ℝ)*(27739/100000 : ℝ)=(10026175880273467/10000000000000000 : ℝ) by norm_num, show 1+2*(33434191970993489/6250000000000000000 : ℝ)=(3158434191970993489/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (272417016817483704329/272430000000000000000 : ℝ)*(X 1 0+X 2 0)+(817996197599/170268750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (31/6250 : ℝ)) (hi := (27739/100000 : ℝ)) (c := (272417016817483704329/272430000000000000000 : ℝ)) (alpha := (817996197599/170268750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (272417016817483704329/272430000000000000000 : ℝ)*(X 0 1+X 2 1)+(817996197599/170268750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (31/6250 : ℝ)) (hi := (27739/100000 : ℝ)) (c := (272417016817483704329/272430000000000000000 : ℝ)) (alpha := (817996197599/170268750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (272417016817483704329/272430000000000000000 : ℝ)*(X 0 2+X 1 2)+(817996197599/170268750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (31/6250 : ℝ)) (hi := (27739/100000 : ℝ)) (c := (272417016817483704329/272430000000000000000 : ℝ)) (alpha := (817996197599/170268750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1044354323/5000000000 : ℝ)*X 0 0+(45569621/80000000 : ℝ)*X 0 1+(5006424411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1083605521/2000000000 : ℝ)*X 1 0+(-615143561/2500000000 : ℝ)*X 1 1+(5006423463/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((338626857/625000000 : ℝ)*X 2 0+(625802693/1250000000 : ℝ)*X 2 1+(-2460573937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((134866863/312500000 : ℝ)*X 0 0+(1840386169/5000000000 : ℝ)*X 0 1+(2529224609/5000000000 : ℝ)*X 0 2+(134866863/312500000 : ℝ)*X 1 0+(1840386169/5000000000 : ℝ)*X 1 1+(2529224609/5000000000 : ℝ)*X 1 2+(134866863/312500000 : ℝ)*X 2 0+(1840386169/5000000000 : ℝ)*X 2 1+(2529224609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2089491699/10000000000 : ℝ)*X 0 0+(626971401/1250000000 : ℝ)*X 0 1+(5686668811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1310251027/2500000000 : ℝ)*X 1 0+(-1780325329/10000000000 : ℝ)*X 1 1+(22213563/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5241003157/10000000000 : ℝ)*X 2 0+(5686673593/10000000000 : ℝ)*X 2 1+(-356064909/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317291867/10000000000 : ℝ)*X 0 0+(2519891597/5000000000 : ℝ)*X 0 1+(3699805393/10000000000 : ℝ)*X 0 2+(4317291867/10000000000 : ℝ)*X 1 0+(2519891597/5000000000 : ℝ)*X 1 1+(3699805393/10000000000 : ℝ)*X 1 2+(4317291867/10000000000 : ℝ)*X 2 0+(2519891597/5000000000 : ℝ)*X 2 1+(3699805393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((5523839/10000000000 : ℝ)*X 0 0+(5490488649/10000000000 : ℝ)*X 0 1+(1587715261/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((49199537/500000000 : ℝ)*X 1 0+(-1099138673/2500000000 : ℝ)*X 1 1+(6945046483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((491991891/5000000000 : ℝ)*X 2 0+(6945029643/10000000000 : ℝ)*X 2 1+(-4396578507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((15308777/80000000 : ℝ)*X 0 0+(2903552957/5000000000 : ℝ)*X 0 1+(2510205191/5000000000 : ℝ)*X 0 2+(15308777/80000000 : ℝ)*X 1 0+(2903552957/5000000000 : ℝ)*X 1 1+(2510205191/5000000000 : ℝ)*X 1 2+(15308777/80000000 : ℝ)*X 2 0+(2903552957/5000000000 : ℝ)*X 2 1+(2510205191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (237582318173173072640702907/63062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (352482989/100000000000000 : ℝ)*(lower2) + (135975255677051/12500000000000 : ℝ)*(major0) + (135975255677051/12500000000000 : ℝ)*(major1) + (135975255677051/12500000000000 : ℝ)*(major2) + (1449741653987937/100000000000000 : ℝ)*(sp0) + (362435221927889/25000000000000 : ℝ)*(sp1) + (724869678304593/50000000000000 : ℝ)*(sp2) + (362929259186693/50000000000000 : ℝ)*(sp3) + (1616112441/50000000000000 : ℝ)*(sp4) + (1660287159/50000000000000 : ℝ)*(sp5) + (1005161559/20000000000000 : ℝ)*(sp6) + (135585389/20000000000000 : ℝ)*(sp9) + (251897919/50000000000000 : ℝ)*(sp10) + (560666251/100000000000000 : ℝ)*(sp11) + (362929539519819/50000000000000 : ℝ)*(f.failure) + (72487244310641/5000000000000 : ℝ)*(f.sum) + (591922147833107/136215000000000000000000000000 : ℝ)*base65 + (27702906851396928779/3405375000000000000000000000000000 : ℝ)*base67 + (31892953548688428779/3405375000000000000000000000000000 : ℝ)*base69 + (48740488778707428779/3405375000000000000000000000000000 : ℝ)*base71 + (21075565234577/8513437500000000000000000000 : ℝ)*base73 + (29655124450889178779/3405375000000000000000000000000000 : ℝ)*base75 + (35452199481585303779/3405375000000000000000000000000000 : ℝ)*base77 + (32966750369347428779/3405375000000000000000000000000000 : ℝ)*base79 + (282641593857767/136215000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2379421/2500000000000000000000 : ℝ)*base90 + (2379421/2500000000000000000000 : ℝ)*base92 + (2379421/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20517596462823100410170211/3941406250000000000000000000000 : ℝ) := by norm_num
    linear_combination (17475184915679/1562500000000 : ℝ)*(major0) + (17475184915679/1562500000000 : ℝ)*(major1) + (17475184915679/1562500000000 : ℝ)*(major2) + (469728657/10000000000000 : ℝ)*(sp1) + (369106469/5000000000000 : ℝ)*(sp2) + (64021573/5000000000000 : ℝ)*(sp3) + (745268050015117/50000000000000 : ℝ)*(sp4) + (745267171312701/50000000000000 : ℝ)*(sp5) + (186316484888959/12500000000000 : ℝ)*(sp6) + (373140744487437/50000000000000 : ℝ)*(sp7) + (820739761/25000000000000 : ℝ)*(sp8) + (171538653/50000000000000 : ℝ)*(sp9) + (121748227/100000000000000 : ℝ)*(sp10) + (2686579/200000000000 : ℝ)*(sp11) + (373142056347917/50000000000000 : ℝ)*(f.failure) + (745269691494639/50000000000000 : ℝ)*(f.sum) + (12429580036477/17026875000000000000000000000 : ℝ)*base66 + (1991304967297750609/425671875000000000000000000000000 : ℝ)*base68 + (2510062005118750609/425671875000000000000000000000000 : ℝ)*base70 + (1320829648197438109/425671875000000000000000000000000 : ℝ)*base72 + (103755830760043/68107500000000000000000000000 : ℝ)*base74 + (2672450910623781859/425671875000000000000000000000000 : ℝ)*base76 + (4036564649914563109/425671875000000000000000000000000 : ℝ)*base78 + (138648871921222187/13302246093750000000000000000000 : ℝ)*base80 + (53285418878891/136215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (26908597/2500000000000000000000 : ℝ)*base89 + (26908597/2500000000000000000000 : ℝ)*base91 + (26908597/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1162_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (31/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5761/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20347/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1162_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1162_s2_0 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267610019/1250000000 : ℝ)*x 0 + (5507040277/10000000000 : ℝ)*x 1 + (5162391919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267610019/1250000000 : ℝ)^8355 ≤ (1622307881737/12500000000000 : ℝ)^6307 := by
    have hnat : (267610019 : ℕ)^8355*12500000000000^6307 ≤ 1622307881737^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267610019 1250000000 1622307881737 12500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5507040277/10000000000 : ℝ)^8355 ≤ (45372175075471/100000000000000 : ℝ)^6307 := by
    have hnat : (5507040277 : ℕ)^8355*100000000000000^6307 ≤ 45372175075471^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507040277 10000000000 45372175075471 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5162391919/10000000000 : ℝ)^8355 ≤ (4164936185173/10000000000000 : ℝ)^6307 := by
    have hnat : (5162391919 : ℕ)^8355*10000000000000^6307 ≤ 4164936185173^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162391919 10000000000 4164936185173 10000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267610019/1250000000 : ℝ), (5507040277/10000000000 : ℝ), (5162391919/10000000000 : ℝ)] ![(1622307881737/12500000000000 : ℝ), (45372175075471/100000000000000 : ℝ), (4164936185173/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267610019/1250000000 : ℝ)|^8355 ≤ (1622307881737/12500000000000 : ℝ)^6307
        have hw : |(-267610019/1250000000 : ℝ)|=(267610019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5507040277/10000000000 : ℝ)|^8355 ≤ (45372175075471/100000000000000 : ℝ)^6307
        have hw : |(5507040277/10000000000 : ℝ)|=(5507040277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5162391919/10000000000 : ℝ)|^8355 ≤ (4164936185173/10000000000000 : ℝ)^6307
        have hw : |(5162391919/10000000000 : ℝ)|=(5162391919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s2_1 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686504159/5000000000 : ℝ)*x 0 + (-2319924279/10000000000 : ℝ)*x 1 + (2581197249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686504159/5000000000 : ℝ)^8355 ≤ (10978781429881/25000000000000 : ℝ)^6307 := by
    have hnat : (2686504159 : ℕ)^8355*25000000000000^6307 ≤ 10978781429881^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686504159 5000000000 10978781429881 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2319924279/10000000000 : ℝ)^8355 ≤ (2887096968631/20000000000000 : ℝ)^6307 := by
    have hnat : (2319924279 : ℕ)^8355*20000000000000^6307 ≤ 2887096968631^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2319924279 10000000000 2887096968631 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2581197249/5000000000 : ℝ)^8355 ≤ (650771709611/1562500000000 : ℝ)^6307 := by
    have hnat : (2581197249 : ℕ)^8355*1562500000000^6307 ≤ 650771709611^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581197249 5000000000 650771709611 1562500000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686504159/5000000000 : ℝ), (-2319924279/10000000000 : ℝ), (2581197249/5000000000 : ℝ)] ![(10978781429881/25000000000000 : ℝ), (2887096968631/20000000000000 : ℝ), (650771709611/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686504159/5000000000 : ℝ)|^8355 ≤ (10978781429881/25000000000000 : ℝ)^6307
        have hw : |(2686504159/5000000000 : ℝ)|=(2686504159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2319924279/10000000000 : ℝ)|^8355 ≤ (2887096968631/20000000000000 : ℝ)^6307
        have hw : |(-2319924279/10000000000 : ℝ)|=(2319924279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2581197249/5000000000 : ℝ)|^8355 ≤ (650771709611/1562500000000 : ℝ)^6307
        have hw : |(2581197249/5000000000 : ℝ)|=(2581197249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s2_2 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5373008661/10000000000 : ℝ)*x 0 + (1032478769/2000000000 : ℝ)*x 1 + (-579981169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373008661/10000000000 : ℝ)^8355 ≤ (43915129433289/100000000000000 : ℝ)^6307 := by
    have hnat : (5373008661 : ℕ)^8355*100000000000000^6307 ≤ 43915129433289^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373008661 10000000000 43915129433289 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032478769/2000000000 : ℝ)^8355 ≤ (41649382436087/100000000000000 : ℝ)^6307 := by
    have hnat : (1032478769 : ℕ)^8355*100000000000000^6307 ≤ 41649382436087^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032478769 2000000000 41649382436087 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579981169/2500000000 : ℝ)^8355 ≤ (2887097623119/20000000000000 : ℝ)^6307 := by
    have hnat : (579981169 : ℕ)^8355*20000000000000^6307 ≤ 2887097623119^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579981169 2500000000 2887097623119 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373008661/10000000000 : ℝ), (1032478769/2000000000 : ℝ), (-579981169/2500000000 : ℝ)] ![(43915129433289/100000000000000 : ℝ), (41649382436087/100000000000000 : ℝ), (2887097623119/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373008661/10000000000 : ℝ)|^8355 ≤ (43915129433289/100000000000000 : ℝ)^6307
        have hw : |(5373008661/10000000000 : ℝ)|=(5373008661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032478769/2000000000 : ℝ)|^8355 ≤ (41649382436087/100000000000000 : ℝ)^6307
        have hw : |(1032478769/2000000000 : ℝ)|=(1032478769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-579981169/2500000000 : ℝ)|^8355 ≤ (2887097623119/20000000000000 : ℝ)^6307
        have hw : |(-579981169/2500000000 : ℝ)|=(579981169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s2_3 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175788757/5000000000 : ℝ)*x 0 + (100520667/250000000 : ℝ)*x 1 + (2354590839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175788757/5000000000 : ℝ)^8355 ≤ (33213038283921/100000000000000 : ℝ)^6307 := by
    have hnat : (2175788757 : ℕ)^8355*100000000000000^6307 ≤ 33213038283921^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175788757 5000000000 33213038283921 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100520667/250000000 : ℝ)^8355 ≤ (186943004773/625000000000 : ℝ)^6307 := by
    have hnat : (100520667 : ℕ)^8355*625000000000^6307 ≤ 186943004773^6307*250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100520667 250000000 186943004773 625000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2354590839/5000000000 : ℝ)^8355 ≤ (4609510117293/12500000000000 : ℝ)^6307 := by
    have hnat : (2354590839 : ℕ)^8355*12500000000000^6307 ≤ 4609510117293^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2354590839 5000000000 4609510117293 12500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175788757/5000000000 : ℝ), (100520667/250000000 : ℝ), (2354590839/5000000000 : ℝ)] ![(33213038283921/100000000000000 : ℝ), (186943004773/625000000000 : ℝ), (4609510117293/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175788757/5000000000 : ℝ)|^8355 ≤ (33213038283921/100000000000000 : ℝ)^6307
        have hw : |(2175788757/5000000000 : ℝ)|=(2175788757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100520667/250000000 : ℝ)|^8355 ≤ (186943004773/625000000000 : ℝ)^6307
        have hw : |(100520667/250000000 : ℝ)|=(100520667/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2354590839/5000000000 : ℝ)|^8355 ≤ (4609510117293/12500000000000 : ℝ)^6307
        have hw : |(2354590839/5000000000 : ℝ)|=(2354590839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s2_4 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140976757/10000000000 : ℝ)*x 0 + (5164735977/10000000000 : ℝ)*x 1 + (5504673481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140976757/10000000000 : ℝ)^8355 ≤ (3244809716843/25000000000000 : ℝ)^6307 := by
    have hnat : (2140976757 : ℕ)^8355*25000000000000^6307 ≤ 3244809716843^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140976757 10000000000 3244809716843 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5164735977/10000000000 : ℝ)^8355 ≤ (41674416099521/100000000000000 : ℝ)^6307 := by
    have hnat : (5164735977 : ℕ)^8355*100000000000000^6307 ≤ 41674416099521^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5164735977 10000000000 41674416099521 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504673481/10000000000 : ℝ)^8355 ≤ (45346345011129/100000000000000 : ℝ)^6307 := by
    have hnat : (5504673481 : ℕ)^8355*100000000000000^6307 ≤ 45346345011129^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504673481 10000000000 45346345011129 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140976757/10000000000 : ℝ), (5164735977/10000000000 : ℝ), (5504673481/10000000000 : ℝ)] ![(3244809716843/25000000000000 : ℝ), (41674416099521/100000000000000 : ℝ), (45346345011129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140976757/10000000000 : ℝ)|^8355 ≤ (3244809716843/25000000000000 : ℝ)^6307
        have hw : |(-2140976757/10000000000 : ℝ)|=(2140976757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5164735977/10000000000 : ℝ)|^8355 ≤ (41674416099521/100000000000000 : ℝ)^6307
        have hw : |(5164735977/10000000000 : ℝ)|=(5164735977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504673481/10000000000 : ℝ)|^8355 ≤ (45346345011129/100000000000000 : ℝ)^6307
        have hw : |(5504673481/10000000000 : ℝ)|=(5504673481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s2_5 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2642722927/5000000000 : ℝ)*x 0 + (-197764421/1000000000 : ℝ)*x 1 + (2752336737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642722927/5000000000 : ℝ)^8355 ≤ (42969578274373/100000000000000 : ℝ)^6307 := by
    have hnat : (2642722927 : ℕ)^8355*100000000000000^6307 ≤ 42969578274373^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642722927 5000000000 42969578274373 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197764421/1000000000 : ℝ)^8355 ≤ (11684076779089/100000000000000 : ℝ)^6307 := by
    have hnat : (197764421 : ℕ)^8355*100000000000000^6307 ≤ 11684076779089^6307*1000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197764421 1000000000 11684076779089 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2752336737/5000000000 : ℝ)^8355 ≤ (2267317246737/5000000000000 : ℝ)^6307 := by
    have hnat : (2752336737 : ℕ)^8355*5000000000000^6307 ≤ 2267317246737^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752336737 5000000000 2267317246737 5000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642722927/5000000000 : ℝ), (-197764421/1000000000 : ℝ), (2752336737/5000000000 : ℝ)] ![(42969578274373/100000000000000 : ℝ), (11684076779089/100000000000000 : ℝ), (2267317246737/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642722927/5000000000 : ℝ)|^8355 ≤ (42969578274373/100000000000000 : ℝ)^6307
        have hw : |(2642722927/5000000000 : ℝ)|=(2642722927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-197764421/1000000000 : ℝ)|^8355 ≤ (11684076779089/100000000000000 : ℝ)^6307
        have hw : |(-197764421/1000000000 : ℝ)|=(197764421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2752336737/5000000000 : ℝ)|^8355 ≤ (2267317246737/5000000000000 : ℝ)^6307
        have hw : |(2752336737/5000000000 : ℝ)|=(2752336737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s2_6 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1321361493/2500000000 : ℝ)*x 0 + (1376168367/2500000000 : ℝ)*x 1 + (-395528811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321361493/2500000000 : ℝ)^8355 ≤ (10742394886299/25000000000000 : ℝ)^6307 := by
    have hnat : (1321361493 : ℕ)^8355*25000000000000^6307 ≤ 10742394886299^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321361493 2500000000 10742394886299 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376168367/2500000000 : ℝ)^8355 ≤ (45346344869263/100000000000000 : ℝ)^6307 := by
    have hnat : (1376168367 : ℕ)^8355*100000000000000^6307 ≤ 45346344869263^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376168367 2500000000 45346344869263 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (395528811/2000000000 : ℝ)^8355 ≤ (467363022639/4000000000000 : ℝ)^6307 := by
    have hnat : (395528811 : ℕ)^8355*4000000000000^6307 ≤ 467363022639^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395528811 2000000000 467363022639 4000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321361493/2500000000 : ℝ), (1376168367/2500000000 : ℝ), (-395528811/2000000000 : ℝ)] ![(10742394886299/25000000000000 : ℝ), (45346344869263/100000000000000 : ℝ), (467363022639/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321361493/2500000000 : ℝ)|^8355 ≤ (10742394886299/25000000000000 : ℝ)^6307
        have hw : |(1321361493/2500000000 : ℝ)|=(1321361493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376168367/2500000000 : ℝ)|^8355 ≤ (45346344869263/100000000000000 : ℝ)^6307
        have hw : |(1376168367/2500000000 : ℝ)|=(1376168367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-395528811/2000000000 : ℝ)|^8355 ≤ (467363022639/4000000000000 : ℝ)^6307
        have hw : |(-395528811/2000000000 : ℝ)|=(395528811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s2_7 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351772053/10000000000 : ℝ)*x 0 + (188180093/400000000 : ℝ)*x 1 + (4025551123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351772053/10000000000 : ℝ)^8355 ≤ (33215005243053/100000000000000 : ℝ)^6307 := by
    have hnat : (4351772053 : ℕ)^8355*100000000000000^6307 ≤ 33215005243053^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351772053 10000000000 33215005243053 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188180093/400000000 : ℝ)^8355 ≤ (36827547768273/100000000000000 : ℝ)^6307 := by
    have hnat : (188180093 : ℕ)^8355*100000000000000^6307 ≤ 36827547768273^6307*400000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188180093 400000000 36827547768273 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4025551123/10000000000 : ℝ)^8355 ≤ (29957446975189/100000000000000 : ℝ)^6307 := by
    have hnat : (4025551123 : ℕ)^8355*100000000000000^6307 ≤ 29957446975189^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025551123 10000000000 29957446975189 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351772053/10000000000 : ℝ), (188180093/400000000 : ℝ), (4025551123/10000000000 : ℝ)] ![(33215005243053/100000000000000 : ℝ), (36827547768273/100000000000000 : ℝ), (29957446975189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351772053/10000000000 : ℝ)|^8355 ≤ (33215005243053/100000000000000 : ℝ)^6307
        have hw : |(4351772053/10000000000 : ℝ)|=(4351772053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(188180093/400000000 : ℝ)|^8355 ≤ (36827547768273/100000000000000 : ℝ)^6307
        have hw : |(188180093/400000000 : ℝ)|=(188180093/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4025551123/10000000000 : ℝ)|^8355 ≤ (29957446975189/100000000000000 : ℝ)^6307
        have hw : |(4025551123/10000000000 : ℝ)|=(4025551123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1162_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20347/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5761/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (229/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4111/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20347/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5761/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20347/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5761/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20347/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5761/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20347/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5761/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20347/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5761/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20347/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5761/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5761/100000 : ℝ) ^ (4177/1024 : ℝ) ≤ (109863886687481/12500000000000000000 : ℝ) := by
    have hpowers : (5761/100000 : ℝ)^4177 ≤ (109863886687481/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5761 : ℕ)^4177*12500000000000000000^1024 ≤ 109863886687481^1024*100000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5761 100000 109863886687481 12500000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5761/100000 : ℝ)) (X := (109863886687481/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20347/100000 : ℝ) ^ (4177/1024 : ℝ) ≤ (4722292262149717/3125000000000000000 : ℝ) := by
    have hpowers : (20347/100000 : ℝ)^4177 ≤ (4722292262149717/3125000000000000000 : ℝ)^1024 := by
      have hnat : (20347 : ℕ)^4177*3125000000000000000^1024 ≤ 4722292262149717^1024*100000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20347 100000 4722292262149717 3125000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20347/100000 : ℝ)) (X := (4722292262149717/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250109863886687481/6250000000000000000 : ℝ) ≤ (5000021546540311/5000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (6250109863886687481/6250000000000000000 : ℝ)^1024 ≤ (5000021546540311/5000000000000000 : ℝ)^4177 := by
      have hnat : (6250109863886687481 : ℕ)^1024*5000000000000000^4177 ≤ 5000021546540311^4177*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250109863886687481 6250000000000000000 5000021546540311 5000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000021546540311/5000000000000000 : ℝ)) (X := (6250109863886687481/6250000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12518999032935286349/12500000000000000000 : ℝ) ≤ (5001861992738249/5000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (12518999032935286349/12500000000000000000 : ℝ)^1024 ≤ (5001861992738249/5000000000000000 : ℝ)^4177 := by
      have hnat : (12518999032935286349 : ℕ)^1024*5000000000000000^4177 ≤ 5001861992738249^4177*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518999032935286349 12500000000000000000 5001861992738249 5000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001861992738249/5000000000000000 : ℝ)) (X := (12518999032935286349/12500000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1567222292262149717/1562500000000000000 : ℝ) ≤ (5003702438936187/5000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (1567222292262149717/1562500000000000000 : ℝ)^1024 ≤ (5003702438936187/5000000000000000 : ℝ)^4177 := by
      have hnat : (1567222292262149717 : ℕ)^1024*5000000000000000^4177 ≤ 5003702438936187^4177*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1567222292262149717 1562500000000000000 5003702438936187 5000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003702438936187/5000000000000000 : ℝ)) (X := (1567222292262149717/1562500000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(109863886687481/12500000000000000000 : ℝ) ≤ ((7290910865674433461/7293000000000000000 : ℝ)+2*(920223098969/364650000000000 : ℝ)*(5761/100000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (7290910865674433461/7293000000000000000 : ℝ)+2*(920223098969/364650000000000 : ℝ)*(5761/100000 : ℝ)=(5000021546540311/5000000000000000 : ℝ) by norm_num, show 1+2*(109863886687481/12500000000000000000 : ℝ)=(6250109863886687481/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4722292262149717/3125000000000000000 : ℝ)+(109863886687481/12500000000000000000 : ℝ) ≤ ((7290910865674433461/7293000000000000000 : ℝ)+(920223098969/364650000000000 : ℝ)*((20347/100000 : ℝ)+(5761/100000 : ℝ)))^(4177/1024 : ℝ) := by
    rw [show (7290910865674433461/7293000000000000000 : ℝ)+(920223098969/364650000000000 : ℝ)*((20347/100000 : ℝ)+(5761/100000 : ℝ))=(5001861992738249/5000000000000000 : ℝ) by norm_num, show 1+(4722292262149717/3125000000000000000 : ℝ)+(109863886687481/12500000000000000000 : ℝ)=(12518999032935286349/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4722292262149717/3125000000000000000 : ℝ) ≤ ((7290910865674433461/7293000000000000000 : ℝ)+2*(920223098969/364650000000000 : ℝ)*(20347/100000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (7290910865674433461/7293000000000000000 : ℝ)+2*(920223098969/364650000000000 : ℝ)*(20347/100000 : ℝ)=(5003702438936187/5000000000000000 : ℝ) by norm_num, show 1+2*(4722292262149717/3125000000000000000 : ℝ)=(1567222292262149717/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7290910865674433461/7293000000000000000 : ℝ)*(X 1 0+X 2 0)+(920223098969/364650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (5761/100000 : ℝ)) (hi := (20347/100000 : ℝ)) (c := (7290910865674433461/7293000000000000000 : ℝ)) (alpha := (920223098969/364650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7290910865674433461/7293000000000000000 : ℝ)*(X 0 1+X 2 1)+(920223098969/364650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (5761/100000 : ℝ)) (hi := (20347/100000 : ℝ)) (c := (7290910865674433461/7293000000000000000 : ℝ)) (alpha := (920223098969/364650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7290910865674433461/7293000000000000000 : ℝ)*(X 0 2+X 1 2)+(920223098969/364650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (5761/100000 : ℝ)) (hi := (20347/100000 : ℝ)) (c := (7290910865674433461/7293000000000000000 : ℝ)) (alpha := (920223098969/364650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-267610019/1250000000 : ℝ)*X 0 0+(5507040277/10000000000 : ℝ)*X 0 1+(5162391919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686504159/5000000000 : ℝ)*X 1 0+(-2319924279/10000000000 : ℝ)*X 1 1+(2581197249/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5373008661/10000000000 : ℝ)*X 2 0+(1032478769/2000000000 : ℝ)*X 2 1+(-579981169/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175788757/5000000000 : ℝ)*X 0 0+(100520667/250000000 : ℝ)*X 0 1+(2354590839/5000000000 : ℝ)*X 0 2+(2175788757/5000000000 : ℝ)*X 1 0+(100520667/250000000 : ℝ)*X 1 1+(2354590839/5000000000 : ℝ)*X 1 2+(2175788757/5000000000 : ℝ)*X 2 0+(100520667/250000000 : ℝ)*X 2 1+(2354590839/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2140976757/10000000000 : ℝ)*X 0 0+(5164735977/10000000000 : ℝ)*X 0 1+(5504673481/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642722927/5000000000 : ℝ)*X 1 0+(-197764421/1000000000 : ℝ)*X 1 1+(2752336737/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321361493/2500000000 : ℝ)*X 2 0+(1376168367/2500000000 : ℝ)*X 2 1+(-395528811/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351772053/10000000000 : ℝ)*X 0 0+(188180093/400000000 : ℝ)*X 0 1+(4025551123/10000000000 : ℝ)*X 0 2+(4351772053/10000000000 : ℝ)*X 1 0+(188180093/400000000 : ℝ)*X 1 1+(4025551123/10000000000 : ℝ)*X 1 2+(4351772053/10000000000 : ℝ)*X 2 0+(188180093/400000000 : ℝ)*X 2 1+(4025551123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72202273665338579444149157/12155000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149335171/50000000000000 : ℝ)*(base19) + (189892283/50000000000000 : ℝ)*(base23) + (87303601/100000000000000 : ℝ)*(upper2) + (4614203/1562500000000 : ℝ)*(upper3) + (14324391/10000000000000 : ℝ)*(upper4) + (217714765346621/10000000000000 : ℝ)*(major0) + (217714765346621/10000000000000 : ℝ)*(major1) + (217714765346621/10000000000000 : ℝ)*(major2) + (362691189983077/12500000000000 : ℝ)*(sp0) + (181346667321369/6250000000000 : ℝ)*(sp1) + (18134666225173/625000000000 : ℝ)*(sp2) + (1452741969448751/100000000000000 : ℝ)*(sp3) + (1745594763/10000000000000 : ℝ)*(sp4) + (6163667101/100000000000000 : ℝ)*(sp7) + (363187033278963/25000000000000 : ℝ)*(f.failure) + (1450773487906123/50000000000000 : ℝ)*(f.sum) + (5053342443271/7293000000000000000000000000 : ℝ)*base65 + (54437314121919637/5610000000000000000000000000000 : ℝ)*base67 + (40893556258239637/5610000000000000000000000000000 : ℝ)*base69 + (7830773834799637/5610000000000000000000000000000 : ℝ)*base71 + (10134501179681/7293000000000000000000000000 : ℝ)*base74 + (44390796272859637/5610000000000000000000000000000 : ℝ)*base75 + (51715677599919637/5610000000000000000000000000000 : ℝ)*base77 + (12398181892539637/5610000000000000000000000000000 : ℝ)*base79 + (32821256589857/7293000000000000000000000000 : ℝ)*base82 + (5046517/1250000000000000000000 : ℝ)*base90 + (5046517/1250000000000000000000 : ℝ)*base92 + (5046517/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13963523322292169266076157/1381250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2220828571/100000000000000 : ℝ)*(base19) + (1193584923/50000000000000 : ℝ)*(base23) + (260321399/100000000000000 : ℝ)*(upper3) + (1495031/5000000000000 : ℝ)*(lower4) + (54904303/25000000000000 : ℝ)*(upper5) + (551822147392743/25000000000000 : ℝ)*(major0) + (551822147392743/25000000000000 : ℝ)*(major1) + (551822147392743/25000000000000 : ℝ)*(major2) + (4300318803/20000000000000 : ℝ)*(sp1) + (24163167139/100000000000000 : ℝ)*(sp2) + (588343305519023/20000000000000 : ℝ)*(sp4) + (2941692805172529/100000000000000 : ℝ)*(sp5) + (294168997725813/10000000000000 : ℝ)*(sp6) + (294572062913777/20000000000000 : ℝ)*(sp7) + (294572062913777/20000000000000 : ℝ)*(f.failure) + (588343305519023/20000000000000 : ℝ)*(f.sum) + (5501196659919/6077500000000000000000000000 : ℝ)*base66 + (55409151482656757/4675000000000000000000000000000 : ℝ)*base67 + (11929750430593243/4675000000000000000000000000000 : ℝ)*base70 + (34566493977481757/4675000000000000000000000000000 : ℝ)*base71 + (18425729398831/6077500000000000000000000000 : ℝ)*base73 + (225811032231757/4675000000000000000000000000000 : ℝ)*base75 + (16621124515956757/4675000000000000000000000000000 : ℝ)*base77 + (46301307413156757/4675000000000000000000000000000 : ℝ)*base79 + (60043441194943/12155000000000000000000000000 : ℝ)*base82 + (2371143/1000000000000000000000 : ℝ)*base90 + (2371143/1000000000000000000000 : ℝ)*base92 + (2371143/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1162_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20347/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5761/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (229/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4111/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1162_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1162_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (229/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4111/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1162_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1162_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1162_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (229/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4111/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1162_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
