-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1239_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:18:05.536433+00:00
-- url     : https://prove2.me/submissions/a86a1d41-cfd2-477c-9757-326d790af3d8

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
theorem support_rectangle_w1239_s3_0 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-3389559/16000000 : ℝ)*x 0 + (541992439/1000000000 : ℝ)*x 1 + (262019257/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3389559/16000000 : ℝ)^527 ≤ (6438432035029/50000000000000 : ℝ)^399 := by
    have hnat : (3389559 : ℕ)^527*50000000000000^399 ≤ 6438432035029^399*16000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3389559 16000000 6438432035029 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541992439/1000000000 : ℝ)^527 ≤ (22265257724823/50000000000000 : ℝ)^399 := by
    have hnat : (541992439 : ℕ)^527*50000000000000^399 ≤ 22265257724823^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541992439 1000000000 22265257724823 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262019257/500000000 : ℝ)^527 ≤ (332754847391/781250000000 : ℝ)^399 := by
    have hnat : (262019257 : ℕ)^527*781250000000^399 ≤ 332754847391^399*500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262019257 500000000 332754847391 781250000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3389559/16000000 : ℝ), (541992439/1000000000 : ℝ), (262019257/500000000 : ℝ)] ![(6438432035029/50000000000000 : ℝ), (22265257724823/50000000000000 : ℝ), (332754847391/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3389559/16000000 : ℝ)|^527 ≤ (6438432035029/50000000000000 : ℝ)^399
        have hw : |(-3389559/16000000 : ℝ)|=(3389559/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541992439/1000000000 : ℝ)|^527 ≤ (22265257724823/50000000000000 : ℝ)^399
        have hw : |(541992439/1000000000 : ℝ)|=(541992439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262019257/500000000 : ℝ)|^527 ≤ (332754847391/781250000000 : ℝ)^399
        have hw : |(262019257/500000000 : ℝ)|=(262019257/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s3_1 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2675778417/5000000000 : ℝ)*x 0 + (-221006941/1000000000 : ℝ)*x 1 + (2620192637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675778417/5000000000 : ℝ)^527 ≤ (10947527274691/25000000000000 : ℝ)^399 := by
    have hnat : (2675778417 : ℕ)^527*25000000000000^399 ≤ 10947527274691^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675778417 5000000000 10947527274691 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221006941/1000000000 : ℝ)^527 ≤ (13617268977523/100000000000000 : ℝ)^399 := by
    have hnat : (221006941 : ℕ)^527*100000000000000^399 ≤ 13617268977523^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221006941 1000000000 13617268977523 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620192637/5000000000 : ℝ)^527 ≤ (42592621904561/100000000000000 : ℝ)^399 := by
    have hnat : (2620192637 : ℕ)^527*100000000000000^399 ≤ 42592621904561^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620192637 5000000000 42592621904561 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675778417/5000000000 : ℝ), (-221006941/1000000000 : ℝ), (2620192637/5000000000 : ℝ)] ![(10947527274691/25000000000000 : ℝ), (13617268977523/100000000000000 : ℝ), (42592621904561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675778417/5000000000 : ℝ)|^527 ≤ (10947527274691/25000000000000 : ℝ)^399
        have hw : |(2675778417/5000000000 : ℝ)|=(2675778417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221006941/1000000000 : ℝ)|^527 ≤ (13617268977523/100000000000000 : ℝ)^399
        have hw : |(-221006941/1000000000 : ℝ)|=(221006941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620192637/5000000000 : ℝ)|^527 ≤ (42592621904561/100000000000000 : ℝ)^399
        have hw : |(2620192637/5000000000 : ℝ)|=(2620192637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s3_2 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2675778373/5000000000 : ℝ)*x 0 + (52403857/100000000 : ℝ)*x 1 + (-552517241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675778373/5000000000 : ℝ)^527 ≤ (8758021629537/20000000000000 : ℝ)^399 := by
    have hnat : (2675778373 : ℕ)^527*20000000000000^399 ≤ 8758021629537^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675778373 5000000000 8758021629537 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52403857/100000000 : ℝ)^527 ≤ (42592626477743/100000000000000 : ℝ)^399 := by
    have hnat : (52403857 : ℕ)^527*100000000000000^399 ≤ 42592626477743^399*100000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52403857 100000000 42592626477743 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552517241/2500000000 : ℝ)^527 ≤ (680863267397/5000000000000 : ℝ)^399 := by
    have hnat : (552517241 : ℕ)^527*5000000000000^399 ≤ 680863267397^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552517241 2500000000 680863267397 5000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675778373/5000000000 : ℝ), (52403857/100000000 : ℝ), (-552517241/2500000000 : ℝ)] ![(8758021629537/20000000000000 : ℝ), (42592626477743/100000000000000 : ℝ), (680863267397/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675778373/5000000000 : ℝ)|^527 ≤ (8758021629537/20000000000000 : ℝ)^399
        have hw : |(2675778373/5000000000 : ℝ)|=(2675778373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52403857/100000000 : ℝ)|^527 ≤ (42592626477743/100000000000000 : ℝ)^399
        have hw : |(52403857/100000000 : ℝ)|=(52403857/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-552517241/2500000000 : ℝ)|^527 ≤ (680863267397/5000000000000 : ℝ)^399
        have hw : |(-552517241/2500000000 : ℝ)|=(552517241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s3_3 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1087367853/2500000000 : ℝ)*x 0 + (4171174403/10000000000 : ℝ)*x 1 + (1133792529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087367853/2500000000 : ℝ)^527 ≤ (16650074576657/50000000000000 : ℝ)^399 := by
    have hnat : (1087367853 : ℕ)^527*50000000000000^399 ≤ 16650074576657^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087367853 2500000000 16650074576657 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171174403/10000000000 : ℝ)^527 ≤ (31509133888199/100000000000000 : ℝ)^399 := by
    have hnat : (4171174403 : ℕ)^527*100000000000000^399 ≤ 31509133888199^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171174403 10000000000 31509133888199 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133792529/2500000000 : ℝ)^527 ≤ (35190716948917/100000000000000 : ℝ)^399 := by
    have hnat : (1133792529 : ℕ)^527*100000000000000^399 ≤ 35190716948917^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133792529 2500000000 35190716948917 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087367853/2500000000 : ℝ), (4171174403/10000000000 : ℝ), (1133792529/2500000000 : ℝ)] ![(16650074576657/50000000000000 : ℝ), (31509133888199/100000000000000 : ℝ), (35190716948917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087367853/2500000000 : ℝ)|^527 ≤ (16650074576657/50000000000000 : ℝ)^399
        have hw : |(1087367853/2500000000 : ℝ)|=(1087367853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171174403/10000000000 : ℝ)|^527 ≤ (31509133888199/100000000000000 : ℝ)^399
        have hw : |(4171174403/10000000000 : ℝ)|=(4171174403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133792529/2500000000 : ℝ)|^527 ≤ (35190716948917/100000000000000 : ℝ)^399
        have hw : |(1133792529/2500000000 : ℝ)|=(1133792529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s3_4 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2118488339/10000000000 : ℝ)*x 0 + (524103881/1000000000 : ℝ)*x 1 + (5419267389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118488339/10000000000 : ℝ)^527 ≤ (12876976177621/100000000000000 : ℝ)^399 := by
    have hnat : (2118488339 : ℕ)^527*100000000000000^399 ≤ 12876976177621^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118488339 10000000000 12876976177621 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524103881/1000000000 : ℝ)^527 ≤ (42599637864167/100000000000000 : ℝ)^399 := by
    have hnat : (524103881 : ℕ)^527*100000000000000^399 ≤ 42599637864167^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524103881 1000000000 42599637864167 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419267389/10000000000 : ℝ)^527 ≤ (22261692968861/50000000000000 : ℝ)^399 := by
    have hnat : (5419267389 : ℕ)^527*50000000000000^399 ≤ 22261692968861^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419267389 10000000000 22261692968861 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2118488339/10000000000 : ℝ), (524103881/1000000000 : ℝ), (5419267389/10000000000 : ℝ)] ![(12876976177621/100000000000000 : ℝ), (42599637864167/100000000000000 : ℝ), (22261692968861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2118488339/10000000000 : ℝ)|^527 ≤ (12876976177621/100000000000000 : ℝ)^399
        have hw : |(-2118488339/10000000000 : ℝ)|=(2118488339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524103881/1000000000 : ℝ)|^527 ≤ (42599637864167/100000000000000 : ℝ)^399
        have hw : |(524103881/1000000000 : ℝ)|=(524103881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419267389/10000000000 : ℝ)|^527 ≤ (22261692968861/50000000000000 : ℝ)^399
        have hw : |(5419267389/10000000000 : ℝ)|=(5419267389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s3_5 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305760299/10000000000 : ℝ)*x 0 + (-1015594257/5000000000 : ℝ)*x 1 + (2709633661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305760299/10000000000 : ℝ)^527 ≤ (43295834240009/100000000000000 : ℝ)^399 := by
    have hnat : (5305760299 : ℕ)^527*100000000000000^399 ≤ 43295834240009^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305760299 10000000000 43295834240009 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015594257/5000000000 : ℝ)^527 ≤ (609039026799/5000000000000 : ℝ)^399 := by
    have hnat : (1015594257 : ℕ)^527*5000000000000^399 ≤ 609039026799^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015594257 5000000000 609039026799 5000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709633661/5000000000 : ℝ)^527 ≤ (44523385210679/100000000000000 : ℝ)^399 := by
    have hnat : (2709633661 : ℕ)^527*100000000000000^399 ≤ 44523385210679^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709633661 5000000000 44523385210679 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305760299/10000000000 : ℝ), (-1015594257/5000000000 : ℝ), (2709633661/5000000000 : ℝ)] ![(43295834240009/100000000000000 : ℝ), (609039026799/5000000000000 : ℝ), (44523385210679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305760299/10000000000 : ℝ)|^527 ≤ (43295834240009/100000000000000 : ℝ)^399
        have hw : |(5305760299/10000000000 : ℝ)|=(5305760299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1015594257/5000000000 : ℝ)|^527 ≤ (609039026799/5000000000000 : ℝ)^399
        have hw : |(-1015594257/5000000000 : ℝ)|=(1015594257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709633661/5000000000 : ℝ)|^527 ≤ (44523385210679/100000000000000 : ℝ)^399
        have hw : |(2709633661/5000000000 : ℝ)|=(2709633661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s3_6 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652881099/5000000000 : ℝ)*x 0 + (2709633021/5000000000 : ℝ)*x 1 + (-507796921/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652881099/5000000000 : ℝ)^527 ≤ (43295854707339/100000000000000 : ℝ)^399 := by
    have hnat : (2652881099 : ℕ)^527*100000000000000^399 ≤ 43295854707339^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652881099 5000000000 43295854707339 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709633021/5000000000 : ℝ)^527 ≤ (22261685660451/50000000000000 : ℝ)^399 := by
    have hnat : (2709633021 : ℕ)^527*50000000000000^399 ≤ 22261685660451^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709633021 5000000000 22261685660451 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507796921/2500000000 : ℝ)^527 ≤ (6090386980907/50000000000000 : ℝ)^399 := by
    have hnat : (507796921 : ℕ)^527*50000000000000^399 ≤ 6090386980907^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507796921 2500000000 6090386980907 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652881099/5000000000 : ℝ), (2709633021/5000000000 : ℝ), (-507796921/2500000000 : ℝ)] ![(43295854707339/100000000000000 : ℝ), (22261685660451/50000000000000 : ℝ), (6090386980907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652881099/5000000000 : ℝ)|^527 ≤ (43295854707339/100000000000000 : ℝ)^399
        have hw : |(2652881099/5000000000 : ℝ)|=(2652881099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709633021/5000000000 : ℝ)|^527 ≤ (22261685660451/50000000000000 : ℝ)^399
        have hw : |(2709633021/5000000000 : ℝ)|=(2709633021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-507796921/2500000000 : ℝ)|^527 ≤ (6090386980907/50000000000000 : ℝ)^399
        have hw : |(-507796921/2500000000 : ℝ)|=(507796921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s3_7 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4349500699/10000000000 : ℝ)*x 0 + (283365307/625000000 : ℝ)*x 1 + (2086252921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349500699/10000000000 : ℝ)^527 ≤ (33300445310841/100000000000000 : ℝ)^399 := by
    have hnat : (4349500699 : ℕ)^527*100000000000000^399 ≤ 33300445310841^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349500699 10000000000 33300445310841 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283365307/625000000 : ℝ)^527 ≤ (35177135858737/100000000000000 : ℝ)^399 := by
    have hnat : (283365307 : ℕ)^527*100000000000000^399 ≤ 35177135858737^399*625000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283365307 625000000 35177135858737 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086252921/5000000000 : ℝ)^527 ≤ (31522418820453/100000000000000 : ℝ)^399 := by
    have hnat : (2086252921 : ℕ)^527*100000000000000^399 ≤ 31522418820453^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086252921 5000000000 31522418820453 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349500699/10000000000 : ℝ), (283365307/625000000 : ℝ), (2086252921/5000000000 : ℝ)] ![(33300445310841/100000000000000 : ℝ), (35177135858737/100000000000000 : ℝ), (31522418820453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349500699/10000000000 : ℝ)|^527 ≤ (33300445310841/100000000000000 : ℝ)^399
        have hw : |(4349500699/10000000000 : ℝ)|=(4349500699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283365307/625000000 : ℝ)|^527 ≤ (35177135858737/100000000000000 : ℝ)^399
        have hw : |(283365307/625000000 : ℝ)|=(283365307/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086252921/5000000000 : ℝ)|^527 ≤ (31522418820453/100000000000000 : ℝ)^399
        have hw : |(2086252921/5000000000 : ℝ)|=(2086252921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1239_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16231/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10903/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (919/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16231/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16231/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16231/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16231/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16231/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16231/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9487/100000 : ℝ) ^ (8431/2048 : ℝ) ≤ (3076928103317649/50000000000000000000 : ℝ) := by
    have hpowers : (9487/100000 : ℝ)^8431 ≤ (3076928103317649/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9487 : ℕ)^8431*50000000000000000000^2048 ≤ 3076928103317649^2048*100000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9487 100000 3076928103317649 50000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9487/100000 : ℝ)) (X := (3076928103317649/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16231/100000 : ℝ) ^ (8431/2048 : ℝ) ≤ (56134391836169411/100000000000000000000 : ℝ) := by
    have hpowers : (16231/100000 : ℝ)^8431 ≤ (56134391836169411/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16231 : ℕ)^8431*100000000000000000000^2048 ≤ 56134391836169411^2048*100000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16231 100000 56134391836169411 100000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16231/100000 : ℝ)) (X := (56134391836169411/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003076928103317649/25000000000000000000 : ℝ) ≤ (5000149478239529/5000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (25003076928103317649/25000000000000000000 : ℝ)^2048 ≤ (5000149478239529/5000000000000000 : ℝ)^8431 := by
      have hnat : (25003076928103317649 : ℕ)^2048*5000000000000000^8431 ≤ 5000149478239529^8431*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003076928103317649 25000000000000000000 5000149478239529 5000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000149478239529/5000000000000000 : ℝ)) (X := (25003076928103317649/25000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100062288248042804709/100000000000000000000 : ℝ) ≤ (10001512706254747/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (100062288248042804709/100000000000000000000 : ℝ)^2048 ≤ (10001512706254747/10000000000000000 : ℝ)^8431 := by
      have hnat : (100062288248042804709 : ℕ)^2048*10000000000000000^8431 ≤ 10001512706254747^8431*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100062288248042804709 100000000000000000000 10001512706254747 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001512706254747/10000000000000000 : ℝ)) (X := (100062288248042804709/100000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50056134391836169411/50000000000000000000 : ℝ) ≤ (2500681614007609/2500000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (50056134391836169411/50000000000000000000 : ℝ)^2048 ≤ (2500681614007609/2500000000000000 : ℝ)^8431 := by
      have hnat : (50056134391836169411 : ℕ)^2048*2500000000000000^8431 ≤ 2500681614007609^8431*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50056134391836169411 50000000000000000000 2500681614007609 2500000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500681614007609/2500000000000000 : ℝ)) (X := (50056134391836169411/50000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3076928103317649/50000000000000000000 : ℝ) ≤ ((11236497745708474011/11240000000000000000 : ℝ)+2*(404583258563/224800000000000 : ℝ)*(9487/100000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (11236497745708474011/11240000000000000000 : ℝ)+2*(404583258563/224800000000000 : ℝ)*(9487/100000 : ℝ)=(5000149478239529/5000000000000000 : ℝ) by norm_num, show 1+2*(3076928103317649/50000000000000000000 : ℝ)=(25003076928103317649/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(56134391836169411/100000000000000000000 : ℝ)+(3076928103317649/50000000000000000000 : ℝ) ≤ ((11236497745708474011/11240000000000000000 : ℝ)+(404583258563/224800000000000 : ℝ)*((16231/100000 : ℝ)+(9487/100000 : ℝ)))^(8431/2048 : ℝ) := by
    rw [show (11236497745708474011/11240000000000000000 : ℝ)+(404583258563/224800000000000 : ℝ)*((16231/100000 : ℝ)+(9487/100000 : ℝ))=(10001512706254747/10000000000000000 : ℝ) by norm_num, show 1+(56134391836169411/100000000000000000000 : ℝ)+(3076928103317649/50000000000000000000 : ℝ)=(100062288248042804709/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(56134391836169411/100000000000000000000 : ℝ) ≤ ((11236497745708474011/11240000000000000000 : ℝ)+2*(404583258563/224800000000000 : ℝ)*(16231/100000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (11236497745708474011/11240000000000000000 : ℝ)+2*(404583258563/224800000000000 : ℝ)*(16231/100000 : ℝ)=(2500681614007609/2500000000000000 : ℝ) by norm_num, show 1+2*(56134391836169411/100000000000000000000 : ℝ)=(50056134391836169411/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11236497745708474011/11240000000000000000 : ℝ)*(X 1 0+X 2 0)+(404583258563/224800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (9487/100000 : ℝ)) (hi := (16231/100000 : ℝ)) (c := (11236497745708474011/11240000000000000000 : ℝ)) (alpha := (404583258563/224800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11236497745708474011/11240000000000000000 : ℝ)*(X 0 1+X 2 1)+(404583258563/224800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (9487/100000 : ℝ)) (hi := (16231/100000 : ℝ)) (c := (11236497745708474011/11240000000000000000 : ℝ)) (alpha := (404583258563/224800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11236497745708474011/11240000000000000000 : ℝ)*(X 0 2+X 1 2)+(404583258563/224800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (9487/100000 : ℝ)) (hi := (16231/100000 : ℝ)) (c := (11236497745708474011/11240000000000000000 : ℝ)) (alpha := (404583258563/224800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-3389559/16000000 : ℝ)*X 0 0+(541992439/1000000000 : ℝ)*X 0 1+(262019257/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675778417/5000000000 : ℝ)*X 1 0+(-221006941/1000000000 : ℝ)*X 1 1+(2620192637/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675778373/5000000000 : ℝ)*X 2 0+(52403857/100000000 : ℝ)*X 2 1+(-552517241/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087367853/2500000000 : ℝ)*X 0 0+(4171174403/10000000000 : ℝ)*X 0 1+(1133792529/2500000000 : ℝ)*X 0 2+(1087367853/2500000000 : ℝ)*X 1 0+(4171174403/10000000000 : ℝ)*X 1 1+(1133792529/2500000000 : ℝ)*X 1 2+(1087367853/2500000000 : ℝ)*X 2 0+(4171174403/10000000000 : ℝ)*X 2 1+(1133792529/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2118488339/10000000000 : ℝ)*X 0 0+(524103881/1000000000 : ℝ)*X 0 1+(5419267389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305760299/10000000000 : ℝ)*X 1 0+(-1015594257/5000000000 : ℝ)*X 1 1+(2709633661/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652881099/5000000000 : ℝ)*X 2 0+(2709633021/5000000000 : ℝ)*X 2 1+(-507796921/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349500699/10000000000 : ℝ)*X 0 0+(283365307/625000000 : ℝ)*X 0 1+(2086252921/5000000000 : ℝ)*X 0 2+(4349500699/10000000000 : ℝ)*X 1 0+(283365307/625000000 : ℝ)*X 1 1+(2086252921/5000000000 : ℝ)*X 1 2+(4349500699/10000000000 : ℝ)*X 2 0+(283365307/625000000 : ℝ)*X 2 1+(2086252921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60105643877295071317179/5620000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1664865187/100000000000000 : ℝ)*(base19) + (296837719/25000000000000 : ℝ)*(base23) + (1613511/781250000000 : ℝ)*(lower2) + (7404333/100000000000000 : ℝ)*(upper3) + (106649569/50000000000000 : ℝ)*(upper5) + (2079303704353209/50000000000000 : ℝ)*(major0) + (2079303704353209/50000000000000 : ℝ)*(major1) + (2079303704353209/50000000000000 : ℝ)*(major2) + (5569849523546707/100000000000000 : ℝ)*(sp0) + (2784947957548849/50000000000000 : ℝ)*(sp1) + (696237049076501/12500000000000 : ℝ)*(sp2) + (1373650901333057/50000000000000 : ℝ)*(sp3) + (48056416177/100000000000000 : ℝ)*(sp4) + (301565707/2000000000000 : ℝ)*(sp7) + (343414610118933/12500000000000 : ℝ)*(f.failure) + (1392474394990721/25000000000000 : ℝ)*(f.sum) + (141871355133/5620000000000000000000000000 : ℝ)*base66 + (7473875150070301299/562000000000000000000000000000000 : ℝ)*base67 + (2706868906640301299/562000000000000000000000000000000 : ℝ)*base69 + (60650071425698701/562000000000000000000000000000000 : ℝ)*base72 + (37103546372227/5620000000000000000000000000 : ℝ)*base73 + (1330321834837698701/562000000000000000000000000000000 : ℝ)*base76 + (3693102135257698701/562000000000000000000000000000000 : ℝ)*base78 + (5996280205070301299/562000000000000000000000000000000 : ℝ)*base79 + (16649875307227/5620000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (214437/78125000000000000000 : ℝ)*base90 + (214437/78125000000000000000 : ℝ)*base92 + (214437/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1716083808236712366072229659/140500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (332445853/100000000000000 : ℝ)*(base19) + (632078683/20000000000000 : ℝ)*(base23) + (29592363/25000000000000 : ℝ)*(lower2) + (57346129/50000000000000 : ℝ)*(upper3) + (74020839/20000000000000 : ℝ)*(lower4) + (77048063/25000000000000 : ℝ)*(upper5) + (2094569709563677/50000000000000 : ℝ)*(major0) + (2094569709563677/50000000000000 : ℝ)*(major1) + (2094569709563677/50000000000000 : ℝ)*(major2) + (5001081771/12500000000000 : ℝ)*(sp2) + (2805395535074101/50000000000000 : ℝ)*(sp4) + (5610790737702349/100000000000000 : ℝ)*(sp5) + (5610747901100619/100000000000000 : ℝ)*(sp6) + (345935920121147/12500000000000 : ℝ)*(sp7) + (345935920121147/12500000000000 : ℝ)*(f.failure) + (2805395535074101/50000000000000 : ℝ)*(f.sum) + (17770221007631/5620000000000000000000000000 : ℝ)*base65 + (9876235550927648447/562000000000000000000000000000000 : ℝ)*base67 + (80542596371648447/562000000000000000000000000000000 : ℝ)*base69 + (3216566886361648447/562000000000000000000000000000000 : ℝ)*base71 + (25828314248031/5620000000000000000000000000 : ℝ)*base73 + (370605601228351553/562000000000000000000000000000000 : ℝ)*base76 + (1967367033443648447/562000000000000000000000000000000 : ℝ)*base77 + (5340469567291648447/562000000000000000000000000000000 : ℝ)*base79 + (9136486067129/5620000000000000000000000000 : ℝ)*base82 + (671683/78125000000000000000 : ℝ)*base90 + (671683/78125000000000000000 : ℝ)*base92 + (671683/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1239_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16231/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10903/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (919/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1239_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1239_s4_0 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060392401/5000000000 : ℝ)*x 0 + (53976219/100000000 : ℝ)*x 1 + (2630586843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060392401/5000000000 : ℝ)^527 ≤ (2579083231773/20000000000000 : ℝ)^399 := by
    have hnat : (1060392401 : ℕ)^527*20000000000000^399 ≤ 2579083231773^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060392401 5000000000 2579083231773 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53976219/100000000 : ℝ)^527 ≤ (11072163234993/25000000000000 : ℝ)^399 := by
    have hnat : (53976219 : ℕ)^527*25000000000000^399 ≤ 11072163234993^399*100000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53976219 100000000 11072163234993 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630586843/5000000000 : ℝ)^527 ≤ (42815930891109/100000000000000 : ℝ)^399 := by
    have hnat : (2630586843 : ℕ)^527*100000000000000^399 ≤ 42815930891109^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630586843 5000000000 42815930891109 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060392401/5000000000 : ℝ), (53976219/100000000 : ℝ), (2630586843/5000000000 : ℝ)] ![(2579083231773/20000000000000 : ℝ), (11072163234993/25000000000000 : ℝ), (42815930891109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060392401/5000000000 : ℝ)|^527 ≤ (2579083231773/20000000000000 : ℝ)^399
        have hw : |(-1060392401/5000000000 : ℝ)|=(1060392401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53976219/100000000 : ℝ)|^527 ≤ (11072163234993/25000000000000 : ℝ)^399
        have hw : |(53976219/100000000 : ℝ)|=(53976219/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630586843/5000000000 : ℝ)|^527 ≤ (42815930891109/100000000000000 : ℝ)^399
        have hw : |(2630586843/5000000000 : ℝ)|=(2630586843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s4_1 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5345936047/10000000000 : ℝ)*x 0 + (-547515917/2500000000 : ℝ)*x 1 + (2630586843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345936047/10000000000 : ℝ)^527 ≤ (43729371510489/100000000000000 : ℝ)^399 := by
    have hnat : (5345936047 : ℕ)^527*100000000000000^399 ≤ 43729371510489^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345936047 10000000000 43729371510489 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547515917/2500000000 : ℝ)^527 ≤ (13454697576473/100000000000000 : ℝ)^399 := by
    have hnat : (547515917 : ℕ)^527*100000000000000^399 ≤ 13454697576473^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547515917 2500000000 13454697576473 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630586843/5000000000 : ℝ)^527 ≤ (42815930891109/100000000000000 : ℝ)^399 := by
    have hnat : (2630586843 : ℕ)^527*100000000000000^399 ≤ 42815930891109^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630586843 5000000000 42815930891109 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345936047/10000000000 : ℝ), (-547515917/2500000000 : ℝ), (2630586843/5000000000 : ℝ)] ![(43729371510489/100000000000000 : ℝ), (13454697576473/100000000000000 : ℝ), (42815930891109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345936047/10000000000 : ℝ)|^527 ≤ (43729371510489/100000000000000 : ℝ)^399
        have hw : |(5345936047/10000000000 : ℝ)|=(5345936047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-547515917/2500000000 : ℝ)|^527 ≤ (13454697576473/100000000000000 : ℝ)^399
        have hw : |(-547515917/2500000000 : ℝ)|=(547515917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630586843/5000000000 : ℝ)|^527 ≤ (42815930891109/100000000000000 : ℝ)^399
        have hw : |(2630586843/5000000000 : ℝ)|=(2630586843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s4_2 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672968043/5000000000 : ℝ)*x 0 + (1315293399/2500000000 : ℝ)*x 1 + (-273757967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672968043/5000000000 : ℝ)^527 ≤ (43729371931847/100000000000000 : ℝ)^399 := by
    have hnat : (2672968043 : ℕ)^527*100000000000000^399 ≤ 43729371931847^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672968043 5000000000 43729371931847 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315293399/2500000000 : ℝ)^527 ≤ (10703982480929/25000000000000 : ℝ)^399 := by
    have hnat : (1315293399 : ℕ)^527*25000000000000^399 ≤ 10703982480929^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315293399 2500000000 10703982480929 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273757967/1250000000 : ℝ)^527 ≤ (13454698128251/100000000000000 : ℝ)^399 := by
    have hnat : (273757967 : ℕ)^527*100000000000000^399 ≤ 13454698128251^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273757967 1250000000 13454698128251 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672968043/5000000000 : ℝ), (1315293399/2500000000 : ℝ), (-273757967/1250000000 : ℝ)] ![(43729371931847/100000000000000 : ℝ), (10703982480929/25000000000000 : ℝ), (13454698128251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672968043/5000000000 : ℝ)|^527 ≤ (43729371931847/100000000000000 : ℝ)^399
        have hw : |(2672968043/5000000000 : ℝ)|=(2672968043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315293399/2500000000 : ℝ)|^527 ≤ (10703982480929/25000000000000 : ℝ)^399
        have hw : |(1315293399/2500000000 : ℝ)|=(1315293399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273757967/1250000000 : ℝ)|^527 ≤ (13454698128251/100000000000000 : ℝ)^399
        have hw : |(-273757967/1250000000 : ℝ)|=(273757967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s4_3 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2175428409/5000000000 : ℝ)*x 0 + (4214678067/10000000000 : ℝ)*x 1 + (4491312673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175428409/5000000000 : ℝ)^527 ≤ (6662831885717/20000000000000 : ℝ)^399 := by
    have hnat : (2175428409 : ℕ)^527*20000000000000^399 ≤ 6662831885717^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175428409 5000000000 6662831885717 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4214678067/10000000000 : ℝ)^527 ≤ (6388782044991/20000000000000 : ℝ)^399 := by
    have hnat : (4214678067 : ℕ)^527*20000000000000^399 ≤ 6388782044991^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214678067 10000000000 6388782044991 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491312673/10000000000 : ℝ)^527 ≤ (8685482584171/25000000000000 : ℝ)^399 := by
    have hnat : (4491312673 : ℕ)^527*25000000000000^399 ≤ 8685482584171^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491312673 10000000000 8685482584171 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175428409/5000000000 : ℝ), (4214678067/10000000000 : ℝ), (4491312673/10000000000 : ℝ)] ![(6662831885717/20000000000000 : ℝ), (6388782044991/20000000000000 : ℝ), (8685482584171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175428409/5000000000 : ℝ)|^527 ≤ (6662831885717/20000000000000 : ℝ)^399
        have hw : |(2175428409/5000000000 : ℝ)|=(2175428409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4214678067/10000000000 : ℝ)|^527 ≤ (6388782044991/20000000000000 : ℝ)^399
        have hw : |(4214678067/10000000000 : ℝ)|=(4214678067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491312673/10000000000 : ℝ)|^527 ≤ (8685482584171/25000000000000 : ℝ)^399
        have hw : |(4491312673/10000000000 : ℝ)|=(4491312673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s4_4 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060395459/5000000000 : ℝ)*x 0 + (328846993/625000000 : ℝ)*x 1 + (21588969/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060395459/5000000000 : ℝ)^527 ≤ (12895465277259/100000000000000 : ℝ)^399 := by
    have hnat : (1060395459 : ℕ)^527*100000000000000^399 ≤ 12895465277259^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060395459 5000000000 12895465277259 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328846993/625000000 : ℝ)^527 ≤ (8563999232043/20000000000000 : ℝ)^399 := by
    have hnat : (328846993 : ℕ)^527*20000000000000^399 ≤ 8563999232043^399*625000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328846993 625000000 8563999232043 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21588969/40000000 : ℝ)^527 ≤ (44284538542581/100000000000000 : ℝ)^399 := by
    have hnat : (21588969 : ℕ)^527*100000000000000^399 ≤ 44284538542581^399*40000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21588969 40000000 44284538542581 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060395459/5000000000 : ℝ), (328846993/625000000 : ℝ), (21588969/40000000 : ℝ)] ![(12895465277259/100000000000000 : ℝ), (8563999232043/20000000000000 : ℝ), (44284538542581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060395459/5000000000 : ℝ)|^527 ≤ (12895465277259/100000000000000 : ℝ)^399
        have hw : |(-1060395459/5000000000 : ℝ)|=(1060395459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328846993/625000000 : ℝ)|^527 ≤ (8563999232043/20000000000000 : ℝ)^399
        have hw : |(328846993/625000000 : ℝ)|=(328846993/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21588969/40000000 : ℝ)|^527 ≤ (44284538542581/100000000000000 : ℝ)^399
        have hw : |(21588969/40000000 : ℝ)|=(21588969/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s4_5 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5311129439/10000000000 : ℝ)*x 0 + (-2053995313/10000000000 : ℝ)*x 1 + (2698621079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311129439/10000000000 : ℝ)^527 ≤ (21676855979431/50000000000000 : ℝ)^399 := by
    have hnat : (5311129439 : ℕ)^527*50000000000000^399 ≤ 21676855979431^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311129439 10000000000 21676855979431 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2053995313/10000000000 : ℝ)^527 ≤ (6180875237461/50000000000000 : ℝ)^399 := by
    have hnat : (2053995313 : ℕ)^527*50000000000000^399 ≤ 6180875237461^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053995313 10000000000 6180875237461 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698621079/5000000000 : ℝ)^527 ≤ (44284537545557/100000000000000 : ℝ)^399 := by
    have hnat : (2698621079 : ℕ)^527*100000000000000^399 ≤ 44284537545557^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698621079 5000000000 44284537545557 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311129439/10000000000 : ℝ), (-2053995313/10000000000 : ℝ), (2698621079/5000000000 : ℝ)] ![(21676855979431/50000000000000 : ℝ), (6180875237461/50000000000000 : ℝ), (44284537545557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311129439/10000000000 : ℝ)|^527 ≤ (21676855979431/50000000000000 : ℝ)^399
        have hw : |(5311129439/10000000000 : ℝ)|=(5311129439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2053995313/10000000000 : ℝ)|^527 ≤ (6180875237461/50000000000000 : ℝ)^399
        have hw : |(-2053995313/10000000000 : ℝ)|=(2053995313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698621079/5000000000 : ℝ)|^527 ≤ (44284537545557/100000000000000 : ℝ)^399
        have hw : |(2698621079/5000000000 : ℝ)|=(2698621079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s4_6 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (331945577/625000000 : ℝ)*x 0 + (1079448503/2000000000 : ℝ)*x 1 + (-2053995107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331945577/625000000 : ℝ)^527 ≤ (21676854863551/50000000000000 : ℝ)^399 := by
    have hnat : (331945577 : ℕ)^527*50000000000000^399 ≤ 21676854863551^399*625000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331945577 625000000 21676854863551 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079448503/2000000000 : ℝ)^527 ≤ (8856908282889/20000000000000 : ℝ)^399 := by
    have hnat : (1079448503 : ℕ)^527*20000000000000^399 ≤ 8856908282889^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079448503 2000000000 8856908282889 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2053995107/10000000000 : ℝ)^527 ≤ (12361748837407/100000000000000 : ℝ)^399 := by
    have hnat : (2053995107 : ℕ)^527*100000000000000^399 ≤ 12361748837407^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053995107 10000000000 12361748837407 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331945577/625000000 : ℝ), (1079448503/2000000000 : ℝ), (-2053995107/10000000000 : ℝ)] ![(21676854863551/50000000000000 : ℝ), (8856908282889/20000000000000 : ℝ), (12361748837407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331945577/625000000 : ℝ)|^527 ≤ (21676854863551/50000000000000 : ℝ)^399
        have hw : |(331945577/625000000 : ℝ)|=(331945577/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079448503/2000000000 : ℝ)|^527 ≤ (8856908282889/20000000000000 : ℝ)^399
        have hw : |(1079448503/2000000000 : ℝ)|=(1079448503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2053995107/10000000000 : ℝ)|^527 ≤ (12361748837407/100000000000000 : ℝ)^399
        have hw : |(-2053995107/10000000000 : ℝ)|=(2053995107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s4_7 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4350869477/10000000000 : ℝ)*x 0 + (561318273/1250000000 : ℝ)*x 1 + (1053861879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350869477/10000000000 : ℝ)^527 ≤ (6662857490517/20000000000000 : ℝ)^399 := by
    have hnat : (4350869477 : ℕ)^527*20000000000000^399 ≤ 6662857490517^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350869477 10000000000 6662857490517 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561318273/1250000000 : ℝ)^527 ≤ (1085440606983/3125000000000 : ℝ)^399 := by
    have hnat : (561318273 : ℕ)^527*3125000000000^399 ≤ 1085440606983^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561318273 1250000000 1085440606983 3125000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053861879/2500000000 : ℝ)^527 ≤ (1597580655969/5000000000000 : ℝ)^399 := by
    have hnat : (1053861879 : ℕ)^527*5000000000000^399 ≤ 1597580655969^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053861879 2500000000 1597580655969 5000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350869477/10000000000 : ℝ), (561318273/1250000000 : ℝ), (1053861879/2500000000 : ℝ)] ![(6662857490517/20000000000000 : ℝ), (1085440606983/3125000000000 : ℝ), (1597580655969/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350869477/10000000000 : ℝ)|^527 ≤ (6662857490517/20000000000000 : ℝ)^399
        have hw : |(4350869477/10000000000 : ℝ)|=(4350869477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561318273/1250000000 : ℝ)|^527 ≤ (1085440606983/3125000000000 : ℝ)^399
        have hw : |(561318273/1250000000 : ℝ)|=(561318273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053861879/2500000000 : ℝ)|^527 ≤ (1597580655969/5000000000000 : ℝ)^399
        have hw : |(1053861879/2500000000 : ℝ)|=(1053861879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1239_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10903/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11347/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (919/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10903/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (919/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10903/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (919/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10903/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (919/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10903/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (919/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10903/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (919/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10903/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10903/100000 : ℝ) ^ (8431/2048 : ℝ) ≤ (10911046832740691/100000000000000000000 : ℝ) := by
    have hpowers : (10903/100000 : ℝ)^8431 ≤ (10911046832740691/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10903 : ℕ)^8431*100000000000000000000^2048 ≤ 10911046832740691^2048*100000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10903 100000 10911046832740691 100000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10903/100000 : ℝ)) (X := (10911046832740691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (919/6250 : ℝ) ^ (8431/2048 : ℝ) ≤ (747501974941263/2000000000000000000 : ℝ) := by
    have hpowers : (919/6250 : ℝ)^8431 ≤ (747501974941263/2000000000000000000 : ℝ)^2048 := by
      have hnat : (919 : ℕ)^8431*2000000000000000000^2048 ≤ 747501974941263^2048*6250^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        919 6250 747501974941263 2000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (919/6250 : ℝ)) (X := (747501974941263/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010911046832740691/50000000000000000000 : ℝ) ≤ (5000265021684827/5000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (50010911046832740691/50000000000000000000 : ℝ)^2048 ≤ (5000265021684827/5000000000000000 : ℝ)^8431 := by
      have hnat : (50010911046832740691 : ℕ)^2048*5000000000000000^8431 ≤ 5000265021684827^8431*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010911046832740691 50000000000000000000 5000265021684827 5000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000265021684827/5000000000000000 : ℝ)) (X := (50010911046832740691/50000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048286145579803841/100000000000000000000 : ℝ) ≤ (2000234543839967/2000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (100048286145579803841/100000000000000000000 : ℝ)^2048 ≤ (2000234543839967/2000000000000000 : ℝ)^8431 := by
      have hnat : (100048286145579803841 : ℕ)^2048*2000000000000000^8431 ≤ 2000234543839967^8431*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048286145579803841 100000000000000000000 2000234543839967 2000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000234543839967/2000000000000000 : ℝ)) (X := (100048286145579803841/100000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000747501974941263/1000000000000000000 : ℝ) ≤ (9767397846709/9765625000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (1000747501974941263/1000000000000000000 : ℝ)^2048 ≤ (9767397846709/9765625000000 : ℝ)^8431 := by
      have hnat : (1000747501974941263 : ℕ)^2048*9765625000000^8431 ≤ 9767397846709^8431*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000747501974941263 1000000000000000000 9767397846709 9765625000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (9767397846709/9765625000000 : ℝ)) (X := (1000747501974941263/1000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10911046832740691/100000000000000000000 : ℝ) ≤ ((56544643609665369/56562500000000000 : ℝ)+2*(30603610961/18100000000000 : ℝ)*(10903/100000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (56544643609665369/56562500000000000 : ℝ)+2*(30603610961/18100000000000 : ℝ)*(10903/100000 : ℝ)=(5000265021684827/5000000000000000 : ℝ) by norm_num, show 1+2*(10911046832740691/100000000000000000000 : ℝ)=(50010911046832740691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(747501974941263/2000000000000000000 : ℝ)+(10911046832740691/100000000000000000000 : ℝ) ≤ ((56544643609665369/56562500000000000 : ℝ)+(30603610961/18100000000000 : ℝ)*((919/6250 : ℝ)+(10903/100000 : ℝ)))^(8431/2048 : ℝ) := by
    rw [show (56544643609665369/56562500000000000 : ℝ)+(30603610961/18100000000000 : ℝ)*((919/6250 : ℝ)+(10903/100000 : ℝ))=(2000234543839967/2000000000000000 : ℝ) by norm_num, show 1+(747501974941263/2000000000000000000 : ℝ)+(10911046832740691/100000000000000000000 : ℝ)=(100048286145579803841/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(747501974941263/2000000000000000000 : ℝ) ≤ ((56544643609665369/56562500000000000 : ℝ)+2*(30603610961/18100000000000 : ℝ)*(919/6250 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (56544643609665369/56562500000000000 : ℝ)+2*(30603610961/18100000000000 : ℝ)*(919/6250 : ℝ)=(9767397846709/9765625000000 : ℝ) by norm_num, show 1+2*(747501974941263/2000000000000000000 : ℝ)=(1000747501974941263/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56544643609665369/56562500000000000 : ℝ)*(X 1 0+X 2 0)+(30603610961/18100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (10903/100000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (56544643609665369/56562500000000000 : ℝ)) (alpha := (30603610961/18100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56544643609665369/56562500000000000 : ℝ)*(X 0 1+X 2 1)+(30603610961/18100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (10903/100000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (56544643609665369/56562500000000000 : ℝ)) (alpha := (30603610961/18100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56544643609665369/56562500000000000 : ℝ)*(X 0 2+X 1 2)+(30603610961/18100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (10903/100000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (56544643609665369/56562500000000000 : ℝ)) (alpha := (30603610961/18100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1060392401/5000000000 : ℝ)*X 0 0+(53976219/100000000 : ℝ)*X 0 1+(2630586843/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345936047/10000000000 : ℝ)*X 1 0+(-547515917/2500000000 : ℝ)*X 1 1+(2630586843/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672968043/5000000000 : ℝ)*X 2 0+(1315293399/2500000000 : ℝ)*X 2 1+(-273757967/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175428409/5000000000 : ℝ)*X 0 0+(4214678067/10000000000 : ℝ)*X 0 1+(4491312673/10000000000 : ℝ)*X 0 2+(2175428409/5000000000 : ℝ)*X 1 0+(4214678067/10000000000 : ℝ)*X 1 1+(4491312673/10000000000 : ℝ)*X 1 2+(2175428409/5000000000 : ℝ)*X 2 0+(4214678067/10000000000 : ℝ)*X 2 1+(4491312673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1060395459/5000000000 : ℝ)*X 0 0+(328846993/625000000 : ℝ)*X 0 1+(21588969/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311129439/10000000000 : ℝ)*X 1 0+(-2053995313/10000000000 : ℝ)*X 1 1+(2698621079/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331945577/625000000 : ℝ)*X 2 0+(1079448503/2000000000 : ℝ)*X 2 1+(-2053995107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350869477/10000000000 : ℝ)*X 0 0+(561318273/1250000000 : ℝ)*X 0 1+(1053861879/2500000000 : ℝ)*X 0 2+(4350869477/10000000000 : ℝ)*X 1 0+(561318273/1250000000 : ℝ)*X 1 1+(1053861879/2500000000 : ℝ)*X 1 2+(4350869477/10000000000 : ℝ)*X 2 0+(561318273/1250000000 : ℝ)*X 2 1+(1053861879/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3033614338227501248853/905000000000000000000000000 : ℝ) := by norm_num
    linear_combination (233520277/25000000000000 : ℝ)*(base19) + (444617953/50000000000000 : ℝ)*(base23) + (97492431/50000000000000 : ℝ)*(upper3) + (6569549/12500000000000 : ℝ)*(upper4) + (31858393/100000000000000 : ℝ)*(upper5) + (5471864290495771/100000000000000 : ℝ)*(major0) + (5471864290495771/100000000000000 : ℝ)*(major1) + (5471864290495771/100000000000000 : ℝ)*(major2) + (7328811419050633/100000000000000 : ℝ)*(sp0) + (916103585760499/12500000000000 : ℝ)*(sp1) + (7328828730929193/100000000000000 : ℝ)*(sp2) + (451860735439623/12500000000000 : ℝ)*(sp3) + (9100557233/50000000000000 : ℝ)*(sp4) + (6482787057/50000000000000 : ℝ)*(sp7) + (1807449424545549/50000000000000 : ℝ)*(f.failure) + (7328829620165099/100000000000000 : ℝ)*(f.sum) + (510879585649/905000000000000000000000000 : ℝ)*base66 + (1503106694531937/2828125000000000000000000000000 : ℝ)*base67 + (25220256786063187/2828125000000000000000000000000 : ℝ)*base69 + (34616657990811813/2828125000000000000000000000000 : ℝ)*base72 + (2321722981491/905000000000000000000000000 : ℝ)*base73 + (4966026059155563/2828125000000000000000000000000 : ℝ)*base76 + (30240452723344437/2828125000000000000000000000000 : ℝ)*base77 + (90640354979218063/2828125000000000000000000000000 : ℝ)*base80 + (2247645331309/905000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6495439/312500000000000000000 : ℝ)*base89 + (6495439/312500000000000000000 : ℝ)*base91 + (6495439/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27398462306736920245523541/2828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (712990321/50000000000000 : ℝ)*(base19) + (22524101/1562500000000 : ℝ)*(base23) + (328967833/100000000000000 : ℝ)*(upper3) + (86114009/100000000000000 : ℝ)*(lower4) + (131787879/100000000000000 : ℝ)*(upper5) + (2751192293300853/50000000000000 : ℝ)*(major0) + (2751192293300853/50000000000000 : ℝ)*(major1) + (2751192293300853/50000000000000 : ℝ)*(major2) + (19076808523/100000000000000 : ℝ)*(sp1) + (20269554609/50000000000000 : ℝ)*(sp2) + (7369707260039299/100000000000000 : ℝ)*(sp4) + (7369686757250133/100000000000000 : ℝ)*(sp5) + (1473933055877523/20000000000000 : ℝ)*(sp6) + (1817530795117813/50000000000000 : ℝ)*(sp7) + (1817530795117813/50000000000000 : ℝ)*(f.failure) + (7369707260039299/100000000000000 : ℝ)*(f.sum) + (2753248192933/452500000000000000000000000 : ℝ)*base65 + (27697389784337691/1414062500000000000000000000000 : ℝ)*base67 + (2433596504442921/353515625000000000000000000000 : ℝ)*base70 + (890732465629783/707031250000000000000000000000 : ℝ)*base71 + (9424801516611/905000000000000000000000000 : ℝ)*base73 + (413421344712691/1414062500000000000000000000000 : ℝ)*base75 + (270850681145169/22094726562500000000000000000 : ℝ)*base77 + (108177170529284757/2828125000000000000000000000000 : ℝ)*base79 + (559960378951/905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (3286257/312500000000000000000 : ℝ)*base90 + (3286257/312500000000000000000 : ℝ)*base92 + (3286257/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1239_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10903/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1239_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1239_s5_0 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-106061887/500000000 : ℝ)*x 0 + (269624193/500000000 : ℝ)*x 1 + (2633007083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106061887/500000000 : ℝ)^527 ≤ (12899053885953/100000000000000 : ℝ)^399 := by
    have hnat : (106061887 : ℕ)^527*100000000000000^399 ≤ 12899053885953^399*500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106061887 500000000 12899053885953 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269624193/500000000 : ℝ)^527 ≤ (44232978112233/100000000000000 : ℝ)^399 := by
    have hnat : (269624193 : ℕ)^527*100000000000000^399 ≤ 44232978112233^399*500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269624193 500000000 44232978112233 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633007083/5000000000 : ℝ)^527 ≤ (42867967977737/100000000000000 : ℝ)^399 := by
    have hnat : (2633007083 : ℕ)^527*100000000000000^399 ≤ 42867967977737^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633007083 5000000000 42867967977737 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106061887/500000000 : ℝ), (269624193/500000000 : ℝ), (2633007083/5000000000 : ℝ)] ![(12899053885953/100000000000000 : ℝ), (44232978112233/100000000000000 : ℝ), (42867967977737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106061887/500000000 : ℝ)|^527 ≤ (12899053885953/100000000000000 : ℝ)^399
        have hw : |(-106061887/500000000 : ℝ)|=(106061887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269624193/500000000 : ℝ)|^527 ≤ (44232978112233/100000000000000 : ℝ)^399
        have hw : |(269624193/500000000 : ℝ)|=(269624193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633007083/5000000000 : ℝ)|^527 ≤ (42867967977737/100000000000000 : ℝ)^399
        have hw : |(2633007083/5000000000 : ℝ)|=(2633007083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s5_1 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1336159221/2500000000 : ℝ)*x 0 + (-17483031/80000000 : ℝ)*x 1 + (5266014141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336159221/2500000000 : ℝ)^527 ≤ (4371533581591/10000000000000 : ℝ)^399 := by
    have hnat : (1336159221 : ℕ)^527*10000000000000^399 ≤ 4371533581591^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336159221 2500000000 4371533581591 10000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17483031/80000000 : ℝ)^527 ≤ (419271764763/3125000000000 : ℝ)^399 := by
    have hnat : (17483031 : ℕ)^527*3125000000000^399 ≤ 419271764763^399*80000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17483031 80000000 419271764763 3125000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266014141/10000000000 : ℝ)^527 ≤ (21433983854469/50000000000000 : ℝ)^399 := by
    have hnat : (5266014141 : ℕ)^527*50000000000000^399 ≤ 21433983854469^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266014141 10000000000 21433983854469 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336159221/2500000000 : ℝ), (-17483031/80000000 : ℝ), (5266014141/10000000000 : ℝ)] ![(4371533581591/10000000000000 : ℝ), (419271764763/3125000000000 : ℝ), (21433983854469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336159221/2500000000 : ℝ)|^527 ≤ (4371533581591/10000000000000 : ℝ)^399
        have hw : |(1336159221/2500000000 : ℝ)|=(1336159221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17483031/80000000 : ℝ)|^527 ≤ (419271764763/3125000000000 : ℝ)^399
        have hw : |(-17483031/80000000 : ℝ)|=(17483031/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266014141/10000000000 : ℝ)|^527 ≤ (21433983854469/50000000000000 : ℝ)^399
        have hw : |(5266014141/10000000000 : ℝ)|=(5266014141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s5_2 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344636741/10000000000 : ℝ)*x 0 + (2633007061/5000000000 : ℝ)*x 1 + (-2185379089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344636741/10000000000 : ℝ)^527 ≤ (43715334271049/100000000000000 : ℝ)^399 := by
    have hnat : (5344636741 : ℕ)^527*100000000000000^399 ≤ 43715334271049^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344636741 10000000000 43715334271049 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633007061/5000000000 : ℝ)^527 ≤ (857359350093/2000000000000 : ℝ)^399 := by
    have hnat : (2633007061 : ℕ)^527*2000000000000^399 ≤ 857359350093^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633007061 5000000000 857359350093 2000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185379089/10000000000 : ℝ)^527 ≤ (134166982077/1000000000000 : ℝ)^399 := by
    have hnat : (2185379089 : ℕ)^527*1000000000000^399 ≤ 134166982077^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185379089 10000000000 134166982077 1000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344636741/10000000000 : ℝ), (2633007061/5000000000 : ℝ), (-2185379089/10000000000 : ℝ)] ![(43715334271049/100000000000000 : ℝ), (857359350093/2000000000000 : ℝ), (134166982077/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344636741/10000000000 : ℝ)|^527 ≤ (43715334271049/100000000000000 : ℝ)^399
        have hw : |(5344636741/10000000000 : ℝ)|=(5344636741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633007061/5000000000 : ℝ)|^527 ≤ (857359350093/2000000000000 : ℝ)^399
        have hw : |(2633007061/5000000000 : ℝ)|=(2633007061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185379089/10000000000 : ℝ)|^527 ≤ (134166982077/1000000000000 : ℝ)^399
        have hw : |(-2185379089/10000000000 : ℝ)|=(2185379089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s5_3 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1087780957/2500000000 : ℝ)*x 0 + (422475889/1000000000 : ℝ)*x 1 + (2240581791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087780957/2500000000 : ℝ)^527 ≤ (6663371960109/20000000000000 : ℝ)^399 := by
    have hnat : (1087780957 : ℕ)^527*20000000000000^399 ≤ 6663371960109^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087780957 2500000000 6663371960109 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422475889/1000000000 : ℝ)^527 ≤ (8011216076203/25000000000000 : ℝ)^399 := by
    have hnat : (422475889 : ℕ)^527*25000000000000^399 ≤ 8011216076203^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422475889 1000000000 8011216076203 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240581791/5000000000 : ℝ)^527 ≤ (6927655175177/20000000000000 : ℝ)^399 := by
    have hnat : (2240581791 : ℕ)^527*20000000000000^399 ≤ 6927655175177^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240581791 5000000000 6927655175177 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087780957/2500000000 : ℝ), (422475889/1000000000 : ℝ), (2240581791/5000000000 : ℝ)] ![(6663371960109/20000000000000 : ℝ), (8011216076203/25000000000000 : ℝ), (6927655175177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087780957/2500000000 : ℝ)|^527 ≤ (6663371960109/20000000000000 : ℝ)^399
        have hw : |(1087780957/2500000000 : ℝ)|=(1087780957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422475889/1000000000 : ℝ)|^527 ≤ (8011216076203/25000000000000 : ℝ)^399
        have hw : |(422475889/1000000000 : ℝ)|=(422475889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240581791/5000000000 : ℝ)|^527 ≤ (6927655175177/20000000000000 : ℝ)^399
        have hw : |(2240581791/5000000000 : ℝ)|=(2240581791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s5_4 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-530310681/2500000000 : ℝ)*x 0 + (1316584771/2500000000 : ℝ)*x 1 + (2696078853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530310681/2500000000 : ℝ)^527 ≤ (6449546957923/50000000000000 : ℝ)^399 := by
    have hnat : (530310681 : ℕ)^527*50000000000000^399 ≤ 6449546957923^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530310681 2500000000 6449546957923 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316584771/2500000000 : ℝ)^527 ≤ (21435730762663/50000000000000 : ℝ)^399 := by
    have hnat : (1316584771 : ℕ)^527*50000000000000^399 ≤ 21435730762663^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316584771 2500000000 21435730762663 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696078853/5000000000 : ℝ)^527 ≤ (5528680567939/12500000000000 : ℝ)^399 := by
    have hnat : (2696078853 : ℕ)^527*12500000000000^399 ≤ 5528680567939^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696078853 5000000000 5528680567939 12500000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-530310681/2500000000 : ℝ), (1316584771/2500000000 : ℝ), (2696078853/5000000000 : ℝ)] ![(6449546957923/50000000000000 : ℝ), (21435730762663/50000000000000 : ℝ), (5528680567939/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-530310681/2500000000 : ℝ)|^527 ≤ (6449546957923/50000000000000 : ℝ)^399
        have hw : |(-530310681/2500000000 : ℝ)|=(530310681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316584771/2500000000 : ℝ)|^527 ≤ (21435730762663/50000000000000 : ℝ)^399
        have hw : |(1316584771/2500000000 : ℝ)|=(1316584771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696078853/5000000000 : ℝ)|^527 ≤ (5528680567939/12500000000000 : ℝ)^399
        have hw : |(2696078853/5000000000 : ℝ)|=(2696078853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s5_5 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1328093577/2500000000 : ℝ)*x 0 + (-2059235393/10000000000 : ℝ)*x 1 + (5392157709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328093577/2500000000 : ℝ)^527 ≤ (10841783488679/25000000000000 : ℝ)^399 := by
    have hnat : (1328093577 : ℕ)^527*25000000000000^399 ≤ 10841783488679^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328093577 2500000000 10841783488679 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059235393/10000000000 : ℝ)^527 ≤ (6201710728711/50000000000000 : ℝ)^399 := by
    have hnat : (2059235393 : ℕ)^527*50000000000000^399 ≤ 6201710728711^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059235393 10000000000 6201710728711 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392157709/10000000000 : ℝ)^527 ≤ (22114722288007/50000000000000 : ℝ)^399 := by
    have hnat : (5392157709 : ℕ)^527*50000000000000^399 ≤ 22114722288007^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392157709 10000000000 22114722288007 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328093577/2500000000 : ℝ), (-2059235393/10000000000 : ℝ), (5392157709/10000000000 : ℝ)] ![(10841783488679/25000000000000 : ℝ), (6201710728711/50000000000000 : ℝ), (22114722288007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328093577/2500000000 : ℝ)|^527 ≤ (10841783488679/25000000000000 : ℝ)^399
        have hw : |(1328093577/2500000000 : ℝ)|=(1328093577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2059235393/10000000000 : ℝ)|^527 ≤ (6201710728711/50000000000000 : ℝ)^399
        have hw : |(-2059235393/10000000000 : ℝ)|=(2059235393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392157709/10000000000 : ℝ)|^527 ≤ (22114722288007/50000000000000 : ℝ)^399
        have hw : |(5392157709/10000000000 : ℝ)|=(5392157709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s5_6 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1062474861/2000000000 : ℝ)*x 0 + (1078431543/2000000000 : ℝ)*x 1 + (-2059235389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062474861/2000000000 : ℝ)^527 ≤ (43367133922369/100000000000000 : ℝ)^399 := by
    have hnat : (1062474861 : ℕ)^527*100000000000000^399 ≤ 43367133922369^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062474861 2000000000 43367133922369 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078431543/2000000000 : ℝ)^527 ≤ (22114722320509/50000000000000 : ℝ)^399 := by
    have hnat : (1078431543 : ℕ)^527*50000000000000^399 ≤ 22114722320509^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078431543 2000000000 22114722320509 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2059235389/10000000000 : ℝ)^527 ≤ (12403421425599/100000000000000 : ℝ)^399 := by
    have hnat : (2059235389 : ℕ)^527*100000000000000^399 ≤ 12403421425599^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059235389 10000000000 12403421425599 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062474861/2000000000 : ℝ), (1078431543/2000000000 : ℝ), (-2059235389/10000000000 : ℝ)] ![(43367133922369/100000000000000 : ℝ), (22114722320509/50000000000000 : ℝ), (12403421425599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062474861/2000000000 : ℝ)|^527 ≤ (43367133922369/100000000000000 : ℝ)^399
        have hw : |(1062474861/2000000000 : ℝ)|=(1062474861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078431543/2000000000 : ℝ)|^527 ≤ (22114722320509/50000000000000 : ℝ)^399
        have hw : |(1078431543/2000000000 : ℝ)|=(1078431543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2059235389/10000000000 : ℝ)|^527 ≤ (12403421425599/100000000000000 : ℝ)^399
        have hw : |(-2059235389/10000000000 : ℝ)|=(2059235389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s5_7 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2175566893/5000000000 : ℝ)*x 0 + (4480504549/10000000000 : ℝ)*x 1 + (2112710207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175566893/5000000000 : ℝ)^527 ≤ (33316960510551/100000000000000 : ℝ)^399 := by
    have hnat : (2175566893 : ℕ)^527*100000000000000^399 ≤ 33316960510551^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175566893 5000000000 33316960510551 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480504549/10000000000 : ℝ)^527 ≤ (6926309531421/20000000000000 : ℝ)^399 := by
    have hnat : (4480504549 : ℕ)^527*20000000000000^399 ≤ 6926309531421^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480504549 10000000000 6926309531421 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112710207/5000000000 : ℝ)^527 ≤ (1001609119379/3125000000000 : ℝ)^399 := by
    have hnat : (2112710207 : ℕ)^527*3125000000000^399 ≤ 1001609119379^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112710207 5000000000 1001609119379 3125000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175566893/5000000000 : ℝ), (4480504549/10000000000 : ℝ), (2112710207/5000000000 : ℝ)] ![(33316960510551/100000000000000 : ℝ), (6926309531421/20000000000000 : ℝ), (1001609119379/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175566893/5000000000 : ℝ)|^527 ≤ (33316960510551/100000000000000 : ℝ)^399
        have hw : |(2175566893/5000000000 : ℝ)|=(2175566893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480504549/10000000000 : ℝ)|^527 ≤ (6926309531421/20000000000000 : ℝ)^399
        have hw : |(4480504549/10000000000 : ℝ)|=(4480504549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112710207/5000000000 : ℝ)|^527 ≤ (1001609119379/3125000000000 : ℝ)^399
        have hw : |(2112710207/5000000000 : ℝ)|=(2112710207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1239_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (229/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14129/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11347/100000 : ℝ) ^ (8431/2048 : ℝ) ≤ (803728917698957/6250000000000000000 : ℝ) := by
    have hpowers : (11347/100000 : ℝ)^8431 ≤ (803728917698957/6250000000000000000 : ℝ)^2048 := by
      have hnat : (11347 : ℕ)^8431*6250000000000000000^2048 ≤ 803728917698957^2048*100000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11347 100000 803728917698957 6250000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11347/100000 : ℝ)) (X := (803728917698957/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (8431/2048 : ℝ) ≤ (16362457935640987/50000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^8431 ≤ (16362457935640987/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14237 : ℕ)^8431*50000000000000000000^2048 ≤ 16362457935640987^2048*100000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 16362457935640987 50000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (16362457935640987/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125803728917698957/3125000000000000000 : ℝ) ≤ (2000124939036707/2000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (3125803728917698957/3125000000000000000 : ℝ)^2048 ≤ (2000124939036707/2000000000000000 : ℝ)^8431 := by
      have hnat : (3125803728917698957 : ℕ)^2048*2000000000000000^8431 ≤ 2000124939036707^8431*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125803728917698957 3125000000000000000 2000124939036707 2000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000124939036707/2000000000000000 : ℝ)) (X := (3125803728917698957/3125000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022792289277232643/50000000000000000000 : ℝ) ≤ (10001107117918353/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (50022792289277232643/50000000000000000000 : ℝ)^2048 ≤ (10001107117918353/10000000000000000 : ℝ)^8431 := by
      have hnat : (50022792289277232643 : ℕ)^2048*10000000000000000^8431 ≤ 10001107117918353^8431*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022792289277232643 50000000000000000000 10001107117918353 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001107117918353/10000000000000000 : ℝ)) (X := (50022792289277232643/50000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016362457935640987/25000000000000000000 : ℝ) ≤ (10001589540653171/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (25016362457935640987/25000000000000000000 : ℝ)^2048 ≤ (10001589540653171/10000000000000000 : ℝ)^8431 := by
      have hnat : (25016362457935640987 : ℕ)^2048*10000000000000000^8431 ≤ 10001589540653171^8431*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016362457935640987 25000000000000000000 10001589540653171 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001589540653171/10000000000000000 : ℝ)) (X := (25016362457935640987/25000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(803728917698957/6250000000000000000 : ℝ) ≤ ((14445428633768228229/14450000000000000000 : ℝ)+2*(241211367409/144500000000000 : ℝ)*(11347/100000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (14445428633768228229/14450000000000000000 : ℝ)+2*(241211367409/144500000000000 : ℝ)*(11347/100000 : ℝ)=(2000124939036707/2000000000000000 : ℝ) by norm_num, show 1+2*(803728917698957/6250000000000000000 : ℝ)=(3125803728917698957/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16362457935640987/50000000000000000000 : ℝ)+(803728917698957/6250000000000000000 : ℝ) ≤ ((14445428633768228229/14450000000000000000 : ℝ)+(241211367409/144500000000000 : ℝ)*((14237/100000 : ℝ)+(11347/100000 : ℝ)))^(8431/2048 : ℝ) := by
    rw [show (14445428633768228229/14450000000000000000 : ℝ)+(241211367409/144500000000000 : ℝ)*((14237/100000 : ℝ)+(11347/100000 : ℝ))=(10001107117918353/10000000000000000 : ℝ) by norm_num, show 1+(16362457935640987/50000000000000000000 : ℝ)+(803728917698957/6250000000000000000 : ℝ)=(50022792289277232643/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16362457935640987/50000000000000000000 : ℝ) ≤ ((14445428633768228229/14450000000000000000 : ℝ)+2*(241211367409/144500000000000 : ℝ)*(14237/100000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (14445428633768228229/14450000000000000000 : ℝ)+2*(241211367409/144500000000000 : ℝ)*(14237/100000 : ℝ)=(10001589540653171/10000000000000000 : ℝ) by norm_num, show 1+2*(16362457935640987/50000000000000000000 : ℝ)=(25016362457935640987/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14445428633768228229/14450000000000000000 : ℝ)*(X 1 0+X 2 0)+(241211367409/144500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14445428633768228229/14450000000000000000 : ℝ)) (alpha := (241211367409/144500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14445428633768228229/14450000000000000000 : ℝ)*(X 0 1+X 2 1)+(241211367409/144500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14445428633768228229/14450000000000000000 : ℝ)) (alpha := (241211367409/144500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14445428633768228229/14450000000000000000 : ℝ)*(X 0 2+X 1 2)+(241211367409/144500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14445428633768228229/14450000000000000000 : ℝ)) (alpha := (241211367409/144500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-106061887/500000000 : ℝ)*X 0 0+(269624193/500000000 : ℝ)*X 0 1+(2633007083/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336159221/2500000000 : ℝ)*X 1 0+(-17483031/80000000 : ℝ)*X 1 1+(5266014141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344636741/10000000000 : ℝ)*X 2 0+(2633007061/5000000000 : ℝ)*X 2 1+(-2185379089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087780957/2500000000 : ℝ)*X 0 0+(422475889/1000000000 : ℝ)*X 0 1+(2240581791/5000000000 : ℝ)*X 0 2+(1087780957/2500000000 : ℝ)*X 1 0+(422475889/1000000000 : ℝ)*X 1 1+(2240581791/5000000000 : ℝ)*X 1 2+(1087780957/2500000000 : ℝ)*X 2 0+(422475889/1000000000 : ℝ)*X 2 1+(2240581791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-530310681/2500000000 : ℝ)*X 0 0+(1316584771/2500000000 : ℝ)*X 0 1+(2696078853/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328093577/2500000000 : ℝ)*X 1 0+(-2059235393/10000000000 : ℝ)*X 1 1+(5392157709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062474861/2000000000 : ℝ)*X 2 0+(1078431543/2000000000 : ℝ)*X 2 1+(-2059235389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175566893/5000000000 : ℝ)*X 0 0+(4480504549/10000000000 : ℝ)*X 0 1+(2112710207/5000000000 : ℝ)*X 0 2+(2175566893/5000000000 : ℝ)*X 1 0+(4480504549/10000000000 : ℝ)*X 1 1+(2112710207/5000000000 : ℝ)*X 1 2+(2175566893/5000000000 : ℝ)*X 2 0+(4480504549/10000000000 : ℝ)*X 2 1+(2112710207/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (492838198592822695907008053/90312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (488900809/50000000000000 : ℝ)*(base19) + (930899077/100000000000000 : ℝ)*(base23) + (40880953/20000000000000 : ℝ)*(upper3) + (5916851/6250000000000 : ℝ)*(lower4) + (737950368097981/12500000000000 : ℝ)*(major0) + (737950368097981/12500000000000 : ℝ)*(major1) + (737950368097981/12500000000000 : ℝ)*(major2) + (7907066758919811/100000000000000 : ℝ)*(sp0) + (1976771176346693/25000000000000 : ℝ)*(sp1) + (7907082686107057/100000000000000 : ℝ)*(sp2) + (975025321898497/25000000000000 : ℝ)*(sp3) + (18924268579/100000000000000 : ℝ)*(sp4) + (129136391/6250000000000 : ℝ)*(sp6) + (9368442123/50000000000000 : ℝ)*(sp7) + (1950060012239117/50000000000000 : ℝ)*(f.failure) + (790708568318839/10000000000000 : ℝ)*(f.sum) + (3313307769483/1806250000000000000000000000 : ℝ)*base65 + (226358833271255649/180625000000000000000000000000000 : ℝ)*base67 + (1791686730577505649/180625000000000000000000000000000 : ℝ)*base69 + (802570754507505649/180625000000000000000000000000000 : ℝ)*base71 + (1554297822591/3612500000000000000000000000 : ℝ)*base73 + (9827363564994351/180625000000000000000000000000000 : ℝ)*base76 + (2485890681205619351/180625000000000000000000000000000 : ℝ)*base78 + (5265837534195005649/180625000000000000000000000000000 : ℝ)*base79 + (40684322693157/7225000000000000000000000000 : ℝ)*base81 + (79513/312500000000000000000 : ℝ)*base90 + (79513/312500000000000000000 : ℝ)*base92 + (79513/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71806728851378498829737577/11289062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1152736121/100000000000000 : ℝ)*(base19) + (1248221579/100000000000000 : ℝ)*(base23) + (130832747/100000000000000 : ℝ)*(upper3) + (43892747/100000000000000 : ℝ)*(lower4) + (15559443/12500000000000 : ℝ)*(upper5) + (185440979164683/3125000000000 : ℝ)*(major0) + (185440979164683/3125000000000 : ℝ)*(major1) + (185440979164683/3125000000000 : ℝ)*(major2) + (1277002919/4000000000000 : ℝ)*(sp1) + (17391060341/50000000000000 : ℝ)*(sp2) + (397397377773471/5000000000000 : ℝ)*(sp4) + (317916579106413/4000000000000 : ℝ)*(sp5) + (7947911525127159/100000000000000 : ℝ)*(sp6) + (1960137449522901/50000000000000 : ℝ)*(sp7) + (1960137449522901/50000000000000 : ℝ)*(f.failure) + (397397377773471/5000000000000 : ℝ)*(f.sum) + (1595589765851/1806250000000000000000000000 : ℝ)*base65 + (92663822354823907/45156250000000000000000000000000 : ℝ)*base67 + (84039521834511407/45156250000000000000000000000000 : ℝ)*base69 + (44258950719511407/45156250000000000000000000000000 : ℝ)*base71 + (4874590401413/903125000000000000000000000 : ℝ)*base73 + (504743085324863593/45156250000000000000000000000000 : ℝ)*base76 + (893878903583105157/45156250000000000000000000000000 : ℝ)*base77 + (664396134676582343/45156250000000000000000000000000 : ℝ)*base80 + (52664583362671/7225000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1952511/312500000000000000000 : ℝ)*base89 + (1952511/312500000000000000000 : ℝ)*base91 + (1952511/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1239_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1239_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1239_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16231/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1239_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1239_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1239_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16231/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1239_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
