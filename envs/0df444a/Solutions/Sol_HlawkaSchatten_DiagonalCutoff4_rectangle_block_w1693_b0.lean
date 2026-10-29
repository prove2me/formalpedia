-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1693_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:39:31.623144+00:00
-- url     : https://prove2.me/submissions/7ea4a240-21df-4791-96a4-ab0dbb0f1935

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
theorem support_rectangle_w1693_s0_0 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69408891/500000000 : ℝ)*x 0 + (5733190693/10000000000 : ℝ)*x 1 + (4941367121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69408891/500000000 : ℝ)^5167 ≤ (8520959391339/100000000000000 : ℝ)^4143 := by
    have hnat : (69408891 : ℕ)^5167*100000000000000^4143 ≤ 8520959391339^4143*500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69408891 500000000 8520959391339 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5733190693/10000000000 : ℝ)^5167 ≤ (9993340698033/20000000000000 : ℝ)^4143 := by
    have hnat : (5733190693 : ℕ)^5167*20000000000000^4143 ≤ 9993340698033^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5733190693 10000000000 9993340698033 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4941367121/10000000000 : ℝ)^5167 ≤ (41512337106261/100000000000000 : ℝ)^4143 := by
    have hnat : (4941367121 : ℕ)^5167*100000000000000^4143 ≤ 41512337106261^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4941367121 10000000000 41512337106261 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69408891/500000000 : ℝ), (5733190693/10000000000 : ℝ), (4941367121/10000000000 : ℝ)] ![(8520959391339/100000000000000 : ℝ), (9993340698033/20000000000000 : ℝ), (41512337106261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69408891/500000000 : ℝ)|^5167 ≤ (8520959391339/100000000000000 : ℝ)^4143
        have hw : |(-69408891/500000000 : ℝ)|=(69408891/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5733190693/10000000000 : ℝ)|^5167 ≤ (9993340698033/20000000000000 : ℝ)^4143
        have hw : |(5733190693/10000000000 : ℝ)|=(5733190693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4941367121/10000000000 : ℝ)|^5167 ≤ (41512337106261/100000000000000 : ℝ)^4143
        have hw : |(4941367121/10000000000 : ℝ)|=(4941367121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s0_1 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5416406447/10000000000 : ℝ)*x 0 + (-227428683/1250000000 : ℝ)*x 1 + (2470684113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416406447/10000000000 : ℝ)^5167 ≤ (9309455440961/20000000000000 : ℝ)^4143 := by
    have hnat : (5416406447 : ℕ)^5167*20000000000000^4143 ≤ 9309455440961^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416406447 10000000000 9309455440961 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227428683/1250000000 : ℝ)^5167 ≤ (1492546762479/12500000000000 : ℝ)^4143 := by
    have hnat : (227428683 : ℕ)^5167*12500000000000^4143 ≤ 1492546762479^4143*1250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227428683 1250000000 1492546762479 12500000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2470684113/5000000000 : ℝ)^5167 ≤ (4151234868379/10000000000000 : ℝ)^4143 := by
    have hnat : (2470684113 : ℕ)^5167*10000000000000^4143 ≤ 4151234868379^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2470684113 5000000000 4151234868379 10000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416406447/10000000000 : ℝ), (-227428683/1250000000 : ℝ), (2470684113/5000000000 : ℝ)] ![(9309455440961/20000000000000 : ℝ), (1492546762479/12500000000000 : ℝ), (4151234868379/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416406447/10000000000 : ℝ)|^5167 ≤ (9309455440961/20000000000000 : ℝ)^4143
        have hw : |(5416406447/10000000000 : ℝ)|=(5416406447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-227428683/1250000000 : ℝ)|^5167 ≤ (1492546762479/12500000000000 : ℝ)^4143
        have hw : |(-227428683/1250000000 : ℝ)|=(227428683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2470684113/5000000000 : ℝ)|^5167 ≤ (4151234868379/10000000000000 : ℝ)^4143
        have hw : |(2470684113/5000000000 : ℝ)|=(2470684113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s0_2 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083281777/2000000000 : ℝ)*x 0 + (4941367249/10000000000 : ℝ)*x 1 + (-1819427523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083281777/2000000000 : ℝ)^5167 ≤ (23273651667429/50000000000000 : ℝ)^4143 := by
    have hnat : (1083281777 : ℕ)^5167*50000000000000^4143 ≤ 23273651667429^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083281777 2000000000 23273651667429 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4941367249/10000000000 : ℝ)^5167 ≤ (5189042305921/12500000000000 : ℝ)^4143 := by
    have hnat : (4941367249 : ℕ)^5167*12500000000000^4143 ≤ 5189042305921^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4941367249 10000000000 5189042305921 12500000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1819427523/10000000000 : ℝ)^5167 ≤ (2985089553301/25000000000000 : ℝ)^4143 := by
    have hnat : (1819427523 : ℕ)^5167*25000000000000^4143 ≤ 2985089553301^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819427523 10000000000 2985089553301 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083281777/2000000000 : ℝ), (4941367249/10000000000 : ℝ), (-1819427523/10000000000 : ℝ)] ![(23273651667429/50000000000000 : ℝ), (5189042305921/12500000000000 : ℝ), (2985089553301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083281777/2000000000 : ℝ)|^5167 ≤ (23273651667429/50000000000000 : ℝ)^4143
        have hw : |(1083281777/2000000000 : ℝ)|=(1083281777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4941367249/10000000000 : ℝ)|^5167 ≤ (5189042305921/12500000000000 : ℝ)^4143
        have hw : |(4941367249/10000000000 : ℝ)|=(4941367249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1819427523/10000000000 : ℝ)|^5167 ≤ (2985089553301/25000000000000 : ℝ)^4143
        have hw : |(-1819427523/10000000000 : ℝ)|=(1819427523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s0_3 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4054036909/10000000000 : ℝ)*x 0 + (3049102513/10000000000 : ℝ)*x 1 + (262798271/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4054036909/10000000000 : ℝ)^5167 ≤ (32431848016703/100000000000000 : ℝ)^4143 := by
    have hnat : (4054036909 : ℕ)^5167*100000000000000^4143 ≤ 32431848016703^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4054036909 10000000000 32431848016703 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3049102513/10000000000 : ℝ)^5167 ≤ (22734111034931/100000000000000 : ℝ)^4143 := by
    have hnat : (3049102513 : ℕ)^5167*100000000000000^4143 ≤ 22734111034931^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3049102513 10000000000 22734111034931 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262798271/500000000 : ℝ)^5167 ≤ (8966808188039/20000000000000 : ℝ)^4143 := by
    have hnat : (262798271 : ℕ)^5167*20000000000000^4143 ≤ 8966808188039^4143*500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262798271 500000000 8966808188039 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4054036909/10000000000 : ℝ), (3049102513/10000000000 : ℝ), (262798271/500000000 : ℝ)] ![(32431848016703/100000000000000 : ℝ), (22734111034931/100000000000000 : ℝ), (8966808188039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4054036909/10000000000 : ℝ)|^5167 ≤ (32431848016703/100000000000000 : ℝ)^4143
        have hw : |(4054036909/10000000000 : ℝ)|=(4054036909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3049102513/10000000000 : ℝ)|^5167 ≤ (22734111034931/100000000000000 : ℝ)^4143
        have hw : |(3049102513/10000000000 : ℝ)|=(3049102513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262798271/500000000 : ℝ)|^5167 ≤ (8966808188039/20000000000000 : ℝ)^4143
        have hw : |(262798271/500000000 : ℝ)|=(262798271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s0_4 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1390132781/10000000000 : ℝ)*x 0 + (4961181569/10000000000 : ℝ)*x 1 + (57126953/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1390132781/10000000000 : ℝ)^5167 ≤ (4267963985137/50000000000000 : ℝ)^4143 := by
    have hnat : (1390132781 : ℕ)^5167*50000000000000^4143 ≤ 4267963985137^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390132781 10000000000 4267963985137 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4961181569/10000000000 : ℝ)^5167 ≤ (41720043811139/100000000000000 : ℝ)^4143 := by
    have hnat : (4961181569 : ℕ)^5167*100000000000000^4143 ≤ 41720043811139^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4961181569 10000000000 41720043811139 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57126953/100000000 : ℝ)^5167 ≤ (49744028209589/100000000000000 : ℝ)^4143 := by
    have hnat : (57126953 : ℕ)^5167*100000000000000^4143 ≤ 49744028209589^4143*100000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57126953 100000000 49744028209589 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1390132781/10000000000 : ℝ), (4961181569/10000000000 : ℝ), (57126953/100000000 : ℝ)] ![(4267963985137/50000000000000 : ℝ), (41720043811139/100000000000000 : ℝ), (49744028209589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1390132781/10000000000 : ℝ)|^5167 ≤ (4267963985137/50000000000000 : ℝ)^4143
        have hw : |(-1390132781/10000000000 : ℝ)|=(1390132781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4961181569/10000000000 : ℝ)|^5167 ≤ (41720043811139/100000000000000 : ℝ)^4143
        have hw : |(4961181569/10000000000 : ℝ)|=(4961181569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(57126953/100000000 : ℝ)|^5167 ≤ (49744028209589/100000000000000 : ℝ)^4143
        have hw : |(57126953/100000000 : ℝ)|=(57126953/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s0_5 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5201387213/10000000000 : ℝ)*x 0 + (-524050729/5000000000 : ℝ)*x 1 + (5712695289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5201387213/10000000000 : ℝ)^5167 ≤ (8850831946001/20000000000000 : ℝ)^4143 := by
    have hnat : (5201387213 : ℕ)^5167*20000000000000^4143 ≤ 8850831946001^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201387213 10000000000 8850831946001 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524050729/5000000000 : ℝ)^5167 ≤ (3000906082463/50000000000000 : ℝ)^4143 := by
    have hnat : (524050729 : ℕ)^5167*50000000000000^4143 ≤ 3000906082463^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524050729 5000000000 3000906082463 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5712695289/10000000000 : ℝ)^5167 ≤ (4974402809013/10000000000000 : ℝ)^4143 := by
    have hnat : (5712695289 : ℕ)^5167*10000000000000^4143 ≤ 4974402809013^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5712695289 10000000000 4974402809013 10000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5201387213/10000000000 : ℝ), (-524050729/5000000000 : ℝ), (5712695289/10000000000 : ℝ)] ![(8850831946001/20000000000000 : ℝ), (3000906082463/50000000000000 : ℝ), (4974402809013/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5201387213/10000000000 : ℝ)|^5167 ≤ (8850831946001/20000000000000 : ℝ)^4143
        have hw : |(5201387213/10000000000 : ℝ)|=(5201387213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524050729/5000000000 : ℝ)|^5167 ≤ (3000906082463/50000000000000 : ℝ)^4143
        have hw : |(-524050729/5000000000 : ℝ)|=(524050729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5712695289/10000000000 : ℝ)|^5167 ≤ (4974402809013/10000000000000 : ℝ)^4143
        have hw : |(5712695289/10000000000 : ℝ)|=(5712695289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s0_6 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2600693617/5000000000 : ℝ)*x 0 + (5712695403/10000000000 : ℝ)*x 1 + (-524050627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2600693617/5000000000 : ℝ)^5167 ≤ (44254159952837/100000000000000 : ℝ)^4143 := by
    have hnat : (2600693617 : ℕ)^5167*100000000000000^4143 ≤ 44254159952837^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600693617 5000000000 44254159952837 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5712695403/10000000000 : ℝ)^5167 ≤ (6218003666019/12500000000000 : ℝ)^4143 := by
    have hnat : (5712695403 : ℕ)^5167*12500000000000^4143 ≤ 6218003666019^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5712695403 10000000000 6218003666019 12500000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524050627/5000000000 : ℝ)^5167 ≤ (375113169251/6250000000000 : ℝ)^4143 := by
    have hnat : (524050627 : ℕ)^5167*6250000000000^4143 ≤ 375113169251^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524050627 5000000000 375113169251 6250000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2600693617/5000000000 : ℝ), (5712695403/10000000000 : ℝ), (-524050627/5000000000 : ℝ)] ![(44254159952837/100000000000000 : ℝ), (6218003666019/12500000000000 : ℝ), (375113169251/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2600693617/5000000000 : ℝ)|^5167 ≤ (44254159952837/100000000000000 : ℝ)^4143
        have hw : |(2600693617/5000000000 : ℝ)|=(2600693617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5712695403/10000000000 : ℝ)|^5167 ≤ (6218003666019/12500000000000 : ℝ)^4143
        have hw : |(5712695403/10000000000 : ℝ)|=(5712695403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524050627/5000000000 : ℝ)|^5167 ≤ (375113169251/6250000000000 : ℝ)^4143
        have hw : |(-524050627/5000000000 : ℝ)|=(524050627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s0_7 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4059485771/10000000000 : ℝ)*x 0 + (5200739207/10000000000 : ℝ)*x 1 + (310622351/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4059485771/10000000000 : ℝ)^5167 ≤ (32486221285379/100000000000000 : ℝ)^4143 := by
    have hnat : (4059485771 : ℕ)^5167*100000000000000^4143 ≤ 32486221285379^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4059485771 10000000000 32486221285379 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5200739207/10000000000 : ℝ)^5167 ≤ (4424728381053/10000000000000 : ℝ)^4143 := by
    have hnat : (5200739207 : ℕ)^5167*10000000000000^4143 ≤ 4424728381053^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200739207 10000000000 4424728381053 10000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310622351/1000000000 : ℝ)^5167 ≤ (11633247443711/50000000000000 : ℝ)^4143 := by
    have hnat : (310622351 : ℕ)^5167*50000000000000^4143 ≤ 11633247443711^4143*1000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310622351 1000000000 11633247443711 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4059485771/10000000000 : ℝ), (5200739207/10000000000 : ℝ), (310622351/1000000000 : ℝ)] ![(32486221285379/100000000000000 : ℝ), (4424728381053/10000000000000 : ℝ), (11633247443711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4059485771/10000000000 : ℝ)|^5167 ≤ (32486221285379/100000000000000 : ℝ)^4143
        have hw : |(4059485771/10000000000 : ℝ)|=(4059485771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5200739207/10000000000 : ℝ)|^5167 ≤ (4424728381053/10000000000000 : ℝ)^4143
        have hw : |(5200739207/10000000000 : ℝ)|=(5200739207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(310622351/1000000000 : ℝ)|^5167 ≤ (11633247443711/50000000000000 : ℝ)^4143
        have hw : |(310622351/1000000000 : ℝ)|=(310622351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1693_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5529/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11263/50000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5159/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5159 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5159*1^1024 ≤ 0^1024*1^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5159/1024 : ℝ) ≤ (30902531658820821/3125000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5159 ≤ (30902531658820821/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5159*3125000000000000000^1024 ≤ 30902531658820821^1024*5^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 30902531658820821 3125000000000000000 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (30902531658820821/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5159 := by
      have hnat : (1 : ℕ)^1024*1^5159 ≤ 1^5159*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3155902531658820821/3125000000000000000 : ℝ) ≤ (10019550781823869/10000000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (3155902531658820821/3125000000000000000 : ℝ)^1024 ≤ (10019550781823869/10000000000000000 : ℝ)^5159 := by
      have hnat : (3155902531658820821 : ℕ)^1024*10000000000000000^5159 ≤ 10019550781823869^5159*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3155902531658820821 3125000000000000000 10019550781823869 10000000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019550781823869/10000000000000000 : ℝ)) (X := (3155902531658820821/3125000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1593402531658820821/1562500000000000000 : ℝ) ≤ (5019550781823869/5000000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (1593402531658820821/1562500000000000000 : ℝ)^1024 ≤ (5019550781823869/5000000000000000 : ℝ)^5159 := by
      have hnat : (1593402531658820821 : ℕ)^1024*5000000000000000^5159 ≤ 5019550781823869^5159*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1593402531658820821 1562500000000000000 5019550781823869 5000000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5019550781823869/5000000000000000 : ℝ)) (X := (1593402531658820821/1562500000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(19550781823869/4000000000000000 : ℝ)*(0 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(19550781823869/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30902531658820821/3125000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(19550781823869/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5159/1024 : ℝ) := by
    rw [show (1 : ℝ)+(19550781823869/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10019550781823869/10000000000000000 : ℝ) by norm_num, show 1+(30902531658820821/3125000000000000000 : ℝ)+(0 : ℝ)=(3155902531658820821/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30902531658820821/3125000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(19550781823869/4000000000000000 : ℝ)*(2/5 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(19550781823869/4000000000000000 : ℝ)*(2/5 : ℝ)=(5019550781823869/5000000000000000 : ℝ) by norm_num, show 1+2*(30902531658820821/3125000000000000000 : ℝ)=(1593402531658820821/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(19550781823869/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19550781823869/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(19550781823869/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19550781823869/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(19550781823869/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19550781823869/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-69408891/500000000 : ℝ)*X 0 0+(5733190693/10000000000 : ℝ)*X 0 1+(4941367121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5416406447/10000000000 : ℝ)*X 1 0+(-227428683/1250000000 : ℝ)*X 1 1+(2470684113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1083281777/2000000000 : ℝ)*X 2 0+(4941367249/10000000000 : ℝ)*X 2 1+(-1819427523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4054036909/10000000000 : ℝ)*X 0 0+(3049102513/10000000000 : ℝ)*X 0 1+(262798271/500000000 : ℝ)*X 0 2+(4054036909/10000000000 : ℝ)*X 1 0+(3049102513/10000000000 : ℝ)*X 1 1+(262798271/500000000 : ℝ)*X 1 2+(4054036909/10000000000 : ℝ)*X 2 0+(3049102513/10000000000 : ℝ)*X 2 1+(262798271/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1390132781/10000000000 : ℝ)*X 0 0+(4961181569/10000000000 : ℝ)*X 0 1+(57126953/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5201387213/10000000000 : ℝ)*X 1 0+(-524050729/5000000000 : ℝ)*X 1 1+(5712695289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2600693617/5000000000 : ℝ)*X 2 0+(5712695403/10000000000 : ℝ)*X 2 1+(-524050627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4059485771/10000000000 : ℝ)*X 0 0+(5200739207/10000000000 : ℝ)*X 0 1+(310622351/1000000000 : ℝ)*X 0 2+(4059485771/10000000000 : ℝ)*X 1 0+(5200739207/10000000000 : ℝ)*X 1 1+(310622351/1000000000 : ℝ)*X 1 2+(4059485771/10000000000 : ℝ)*X 2 0+(5200739207/10000000000 : ℝ)*X 2 1+(310622351/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (973283797325420194454811/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8742123/50000000000000 : ℝ)*(base1) + (298431801/20000000000000 : ℝ)*(base19) + (961511837/50000000000000 : ℝ)*(base23) + (137594671/100000000000000 : ℝ)*(base24) + (197955227/50000000000000 : ℝ)*(upper5) + (858032153232573/100000000000000 : ℝ)*(major0) + (858032153232573/100000000000000 : ℝ)*(major1) + (858032153232573/100000000000000 : ℝ)*(major2) + (126291382568569/10000000000000 : ℝ)*(sp0) + (15786547492209/1250000000000 : ℝ)*(sp1) + (63146161545869/5000000000000 : ℝ)*(sp2) + (453135632186711/100000000000000 : ℝ)*(sp3) + (5741667141/50000000000000 : ℝ)*(sp4) + (3040830523/100000000000000 : ℝ)*(sp7) + (453138690501481/100000000000000 : ℝ)*(f.failure) + (631462645767863/50000000000000 : ℝ)*(f.sum) + (66281018315063/200000000000000000000000000000 : ℝ)*base66 + (1342859573115063/400000000000000000000000000000 : ℝ)*base68 + (1999160103684937/400000000000000000000000000000 : ℝ)*base69 + (287233730884937/400000000000000000000000000000 : ℝ)*base71 + (991167305115063/200000000000000000000000000000 : ℝ)*base74 + (2856909851684937/400000000000000000000000000000 : ℝ)*base75 + (890049253115063/400000000000000000000000000000 : ℝ)*base78 + (1464598030084937/400000000000000000000000000000 : ℝ)*base79 + (782494842315063/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8560381/10000000000000000000000 : ℝ)*base90 + (8560381/10000000000000000000000 : ℝ)*base92 + (8560381/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32758731846140253852471/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (276306367/12500000000000 : ℝ)*(base19) + (560519809/25000000000000 : ℝ)*(base23) + (12020277/20000000000000 : ℝ)*(base32) + (91007071/25000000000000 : ℝ)*(upper3) + (149700711/50000000000000 : ℝ)*(upper5) + (14125662244797/1562500000000 : ℝ)*(major0) + (14125662244797/1562500000000 : ℝ)*(major1) + (14125662244797/1562500000000 : ℝ)*(major2) + (3773987091/50000000000000 : ℝ)*(sp1) + (1636604609/20000000000000 : ℝ)*(sp2) + (41582721438867/3125000000000 : ℝ)*(sp4) + (665318663809313/50000000000000 : ℝ)*(sp5) + (1330636660941463/100000000000000 : ℝ)*(sp6) + (59679658970301/12500000000000 : ℝ)*(sp7) + (238718665931897/50000000000000 : ℝ)*(f.failure) + (41582721438867/3125000000000 : ℝ)*(f.sum) + (4657151584593/3125000000000000000000000000 : ℝ)*base65 + (45171385709593/6250000000000000000000000000 : ℝ)*base67 + (27779429840407/6250000000000000000000000000 : ℝ)*base70 + (5013932784593/6250000000000000000000000000 : ℝ)*base71 + (22721680347093/3125000000000000000000000000 : ℝ)*base73 + (2771872627907/6250000000000000000000000000 : ℝ)*base76 + (26085176434157/6250000000000000000000000000 : ℝ)*base78 + (58628301597093/6250000000000000000000000000 : ℝ)*base79 + (831307706141/1562500000000000000000000000 : ℝ)*base82 + (19898803/5000000000000000000000 : ℝ)*base89 + (19898803/5000000000000000000000 : ℝ)*base91 + (19898803/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1693_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5529/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11263/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1693_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1693_s1_0 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1470693629/10000000000 : ℝ)*x 0 + (5502276799/10000000000 : ℝ)*x 1 + (511821453/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1470693629/10000000000 : ℝ)^5167 ≤ (2289305598519/25000000000000 : ℝ)^4143 := by
    have hnat : (1470693629 : ℕ)^5167*25000000000000^4143 ≤ 2289305598519^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470693629 10000000000 2289305598519 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502276799/10000000000 : ℝ)^5167 ≤ (1898776657967/4000000000000 : ℝ)^4143 := by
    have hnat : (5502276799 : ℕ)^5167*4000000000000^4143 ≤ 1898776657967^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502276799 10000000000 1898776657967 4000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511821453/1000000000 : ℝ)^5167 ≤ (21686680576513/50000000000000 : ℝ)^4143 := by
    have hnat : (511821453 : ℕ)^5167*50000000000000^4143 ≤ 21686680576513^4143*1000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511821453 1000000000 21686680576513 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1470693629/10000000000 : ℝ), (5502276799/10000000000 : ℝ), (511821453/1000000000 : ℝ)] ![(2289305598519/25000000000000 : ℝ), (1898776657967/4000000000000 : ℝ), (21686680576513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1470693629/10000000000 : ℝ)|^5167 ≤ (2289305598519/25000000000000 : ℝ)^4143
        have hw : |(-1470693629/10000000000 : ℝ)|=(1470693629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502276799/10000000000 : ℝ)|^5167 ≤ (1898776657967/4000000000000 : ℝ)^4143
        have hw : |(5502276799/10000000000 : ℝ)|=(5502276799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(511821453/1000000000 : ℝ)|^5167 ≤ (21686680576513/50000000000000 : ℝ)^4143
        have hw : |(511821453/1000000000 : ℝ)|=(511821453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s1_1 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677444977/5000000000 : ℝ)*x 0 + (-52217731/312500000 : ℝ)*x 1 + (5118214137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677444977/5000000000 : ℝ)^5167 ≤ (22944441202981/50000000000000 : ℝ)^4143 := by
    have hnat : (2677444977 : ℕ)^5167*50000000000000^4143 ≤ 22944441202981^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677444977 5000000000 22944441202981 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52217731/312500000 : ℝ)^5167 ≤ (2684440145203/25000000000000 : ℝ)^4143 := by
    have hnat : (52217731 : ℕ)^5167*25000000000000^4143 ≤ 2684440145203^4143*312500000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52217731 312500000 2684440145203 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5118214137/10000000000 : ℝ)^5167 ≤ (5421669624933/12500000000000 : ℝ)^4143 := by
    have hnat : (5118214137 : ℕ)^5167*12500000000000^4143 ≤ 5421669624933^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5118214137 10000000000 5421669624933 12500000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677444977/5000000000 : ℝ), (-52217731/312500000 : ℝ), (5118214137/10000000000 : ℝ)] ![(22944441202981/50000000000000 : ℝ), (2684440145203/25000000000000 : ℝ), (5421669624933/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677444977/5000000000 : ℝ)|^5167 ≤ (22944441202981/50000000000000 : ℝ)^4143
        have hw : |(2677444977/5000000000 : ℝ)|=(2677444977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52217731/312500000 : ℝ)|^5167 ≤ (2684440145203/25000000000000 : ℝ)^4143
        have hw : |(-52217731/312500000 : ℝ)|=(52217731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5118214137/10000000000 : ℝ)|^5167 ≤ (5421669624933/12500000000000 : ℝ)^4143
        have hw : |(5118214137/10000000000 : ℝ)|=(5118214137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s1_2 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677444519/5000000000 : ℝ)*x 0 + (5118214931/10000000000 : ℝ)*x 1 + (-835483783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677444519/5000000000 : ℝ)^5167 ≤ (9177774523223/20000000000000 : ℝ)^4143 := by
    have hnat : (2677444519 : ℕ)^5167*20000000000000^4143 ≤ 9177774523223^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677444519 5000000000 9177774523223 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5118214931/10000000000 : ℝ)^5167 ≤ (21686682695569/50000000000000 : ℝ)^4143 := by
    have hnat : (5118214931 : ℕ)^5167*50000000000000^4143 ≤ 21686682695569^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5118214931 10000000000 21686682695569 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (835483783/5000000000 : ℝ)^5167 ≤ (671110123457/6250000000000 : ℝ)^4143 := by
    have hnat : (835483783 : ℕ)^5167*6250000000000^4143 ≤ 671110123457^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835483783 5000000000 671110123457 6250000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677444519/5000000000 : ℝ), (5118214931/10000000000 : ℝ), (-835483783/5000000000 : ℝ)] ![(9177774523223/20000000000000 : ℝ), (21686682695569/50000000000000 : ℝ), (671110123457/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677444519/5000000000 : ℝ)|^5167 ≤ (9177774523223/20000000000000 : ℝ)^4143
        have hw : |(2677444519/5000000000 : ℝ)|=(2677444519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5118214931/10000000000 : ℝ)|^5167 ≤ (21686682695569/50000000000000 : ℝ)^4143
        have hw : |(5118214931/10000000000 : ℝ)|=(5118214931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-835483783/5000000000 : ℝ)|^5167 ≤ (671110123457/6250000000000 : ℝ)^4143
        have hw : |(-835483783/5000000000 : ℝ)|=(835483783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s1_3 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (824624449/2000000000 : ℝ)*x 0 + (9027233/25000000 : ℝ)*x 1 + (1170324613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (824624449/2000000000 : ℝ)^5167 ≤ (16561284919943/50000000000000 : ℝ)^4143 := by
    have hnat : (824624449 : ℕ)^5167*50000000000000^4143 ≤ 16561284919943^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824624449 2000000000 16561284919943 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9027233/25000000 : ℝ)^5167 ≤ (5614394857353/20000000000000 : ℝ)^4143 := by
    have hnat : (9027233 : ℕ)^5167*20000000000000^4143 ≤ 5614394857353^4143*25000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9027233 25000000 5614394857353 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1170324613/2500000000 : ℝ)^5167 ≤ (38805455863311/100000000000000 : ℝ)^4143 := by
    have hnat : (1170324613 : ℕ)^5167*100000000000000^4143 ≤ 38805455863311^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170324613 2500000000 38805455863311 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(824624449/2000000000 : ℝ), (9027233/25000000 : ℝ), (1170324613/2500000000 : ℝ)] ![(16561284919943/50000000000000 : ℝ), (5614394857353/20000000000000 : ℝ), (38805455863311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(824624449/2000000000 : ℝ)|^5167 ≤ (16561284919943/50000000000000 : ℝ)^4143
        have hw : |(824624449/2000000000 : ℝ)|=(824624449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9027233/25000000 : ℝ)|^5167 ≤ (5614394857353/20000000000000 : ℝ)^4143
        have hw : |(9027233/25000000 : ℝ)|=(9027233/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1170324613/2500000000 : ℝ)|^5167 ≤ (38805455863311/100000000000000 : ℝ)^4143
        have hw : |(1170324613/2500000000 : ℝ)|=(1170324613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s1_4 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-735456639/5000000000 : ℝ)*x 0 + (640358877/1250000000 : ℝ)*x 1 + (2748771651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (735456639/5000000000 : ℝ)^5167 ≤ (9158928092801/100000000000000 : ℝ)^4143 := by
    have hnat : (735456639 : ℕ)^5167*100000000000000^4143 ≤ 9158928092801^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735456639 5000000000 9158928092801 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640358877/1250000000 : ℝ)^5167 ≤ (21711290215479/50000000000000 : ℝ)^4143 := by
    have hnat : (640358877 : ℕ)^5167*50000000000000^4143 ≤ 21711290215479^4143*1250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640358877 1250000000 21711290215479 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2748771651/5000000000 : ℝ)^5167 ≤ (47418491464317/100000000000000 : ℝ)^4143 := by
    have hnat : (2748771651 : ℕ)^5167*100000000000000^4143 ≤ 47418491464317^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748771651 5000000000 47418491464317 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-735456639/5000000000 : ℝ), (640358877/1250000000 : ℝ), (2748771651/5000000000 : ℝ)] ![(9158928092801/100000000000000 : ℝ), (21711290215479/50000000000000 : ℝ), (47418491464317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-735456639/5000000000 : ℝ)|^5167 ≤ (9158928092801/100000000000000 : ℝ)^4143
        have hw : |(-735456639/5000000000 : ℝ)|=(735456639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640358877/1250000000 : ℝ)|^5167 ≤ (21711290215479/50000000000000 : ℝ)^4143
        have hw : |(640358877/1250000000 : ℝ)|=(640358877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2748771651/5000000000 : ℝ)|^5167 ≤ (47418491464317/100000000000000 : ℝ)^4143
        have hw : |(2748771651/5000000000 : ℝ)|=(2748771651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s1_5 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050424121/2000000000 : ℝ)*x 0 + (-1291637321/10000000000 : ℝ)*x 1 + (1374385727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050424121/2000000000 : ℝ)^5167 ≤ (895862834281/2000000000000 : ℝ)^4143 := by
    have hnat : (1050424121 : ℕ)^5167*2000000000000^4143 ≤ 895862834281^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050424121 2000000000 895862834281 2000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1291637321/10000000000 : ℝ)^5167 ≤ (3894185524513/50000000000000 : ℝ)^4143 := by
    have hnat : (1291637321 : ℕ)^5167*50000000000000^4143 ≤ 3894185524513^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291637321 10000000000 3894185524513 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1374385727/2500000000 : ℝ)^5167 ≤ (47418487225947/100000000000000 : ℝ)^4143 := by
    have hnat : (1374385727 : ℕ)^5167*100000000000000^4143 ≤ 47418487225947^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374385727 2500000000 47418487225947 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050424121/2000000000 : ℝ), (-1291637321/10000000000 : ℝ), (1374385727/2500000000 : ℝ)] ![(895862834281/2000000000000 : ℝ), (3894185524513/50000000000000 : ℝ), (47418487225947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050424121/2000000000 : ℝ)|^5167 ≤ (895862834281/2000000000000 : ℝ)^4143
        have hw : |(1050424121/2000000000 : ℝ)|=(1050424121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1291637321/10000000000 : ℝ)|^5167 ≤ (3894185524513/50000000000000 : ℝ)^4143
        have hw : |(-1291637321/10000000000 : ℝ)|=(1291637321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1374385727/2500000000 : ℝ)|^5167 ≤ (47418487225947/100000000000000 : ℝ)^4143
        have hw : |(1374385727/2500000000 : ℝ)|=(1374385727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s1_6 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525211987/1000000000 : ℝ)*x 0 + (5497543179/10000000000 : ℝ)*x 1 + (-322909493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525211987/1000000000 : ℝ)^5167 ≤ (22396566948097/50000000000000 : ℝ)^4143 := by
    have hnat : (525211987 : ℕ)^5167*50000000000000^4143 ≤ 22396566948097^4143*1000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525211987 1000000000 22396566948097 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497543179/10000000000 : ℝ)^5167 ≤ (47418490141171/100000000000000 : ℝ)^4143 := by
    have hnat : (5497543179 : ℕ)^5167*100000000000000^4143 ≤ 47418490141171^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497543179 10000000000 47418490141171 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322909493/2500000000 : ℝ)^5167 ≤ (3894187972339/50000000000000 : ℝ)^4143 := by
    have hnat : (322909493 : ℕ)^5167*50000000000000^4143 ≤ 3894187972339^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322909493 2500000000 3894187972339 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525211987/1000000000 : ℝ), (5497543179/10000000000 : ℝ), (-322909493/2500000000 : ℝ)] ![(22396566948097/50000000000000 : ℝ), (47418490141171/100000000000000 : ℝ), (3894187972339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525211987/1000000000 : ℝ)|^5167 ≤ (22396566948097/50000000000000 : ℝ)^4143
        have hw : |(525211987/1000000000 : ℝ)|=(525211987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497543179/10000000000 : ℝ)|^5167 ≤ (47418490141171/100000000000000 : ℝ)^4143
        have hw : |(5497543179/10000000000 : ℝ)|=(5497543179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-322909493/2500000000 : ℝ)|^5167 ≤ (3894187972339/50000000000000 : ℝ)^4143
        have hw : |(-322909493/2500000000 : ℝ)|=(322909493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s1_7 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4123735613/10000000000 : ℝ)*x 0 + (4668321119/10000000000 : ℝ)*x 1 + (906021513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4123735613/10000000000 : ℝ)^5167 ≤ (258818087843/781250000000 : ℝ)^4143 := by
    have hnat : (4123735613 : ℕ)^5167*781250000000^4143 ≤ 258818087843^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123735613 10000000000 258818087843 781250000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4668321119/10000000000 : ℝ)^5167 ≤ (38671338031857/100000000000000 : ℝ)^4143 := by
    have hnat : (4668321119 : ℕ)^5167*100000000000000^4143 ≤ 38671338031857^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4668321119 10000000000 38671338031857 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906021513/2500000000 : ℝ)^5167 ≤ (14099973356319/50000000000000 : ℝ)^4143 := by
    have hnat : (906021513 : ℕ)^5167*50000000000000^4143 ≤ 14099973356319^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906021513 2500000000 14099973356319 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4123735613/10000000000 : ℝ), (4668321119/10000000000 : ℝ), (906021513/2500000000 : ℝ)] ![(258818087843/781250000000 : ℝ), (38671338031857/100000000000000 : ℝ), (14099973356319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4123735613/10000000000 : ℝ)|^5167 ≤ (258818087843/781250000000 : ℝ)^4143
        have hw : |(4123735613/10000000000 : ℝ)|=(4123735613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4668321119/10000000000 : ℝ)|^5167 ≤ (38671338031857/100000000000000 : ℝ)^4143
        have hw : |(4668321119/10000000000 : ℝ)|=(4668321119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(906021513/2500000000 : ℝ)|^5167 ≤ (14099973356319/50000000000000 : ℝ)^4143
        have hw : |(906021513/2500000000 : ℝ)|=(906021513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1693_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11263/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5529/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9477/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2207/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11263/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5529/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11263/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5529/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11263/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5529/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11263/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5529/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11263/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5529/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11263/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5529/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5529/100000 : ℝ) ^ (5159/1024 : ℝ) ≤ (23137448795247/50000000000000000000 : ℝ) := by
    have hpowers : (5529/100000 : ℝ)^5159 ≤ (23137448795247/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5529 : ℕ)^5159*50000000000000000000^1024 ≤ 23137448795247^1024*100000^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5529 100000 23137448795247 50000000000000000000 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5529/100000 : ℝ)) (X := (23137448795247/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11263/50000 : ℝ) ^ (5159/1024 : ℝ) ≤ (27399129784415831/50000000000000000000 : ℝ) := by
    have hpowers : (11263/50000 : ℝ)^5159 ≤ (27399129784415831/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11263 : ℕ)^5159*50000000000000000000^1024 ≤ 27399129784415831^1024*50000^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11263 50000 27399129784415831 50000000000000000000 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11263/50000 : ℝ)) (X := (27399129784415831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000023137448795247/25000000000000000000 : ℝ) ≤ (5000000918501213/5000000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (25000023137448795247/25000000000000000000 : ℝ)^1024 ≤ (5000000918501213/5000000000000000 : ℝ)^5159 := by
      have hnat : (25000023137448795247 : ℕ)^1024*5000000000000000^5159 ≤ 5000000918501213^5159*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000023137448795247 25000000000000000000 5000000918501213 5000000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000918501213/5000000000000000 : ℝ)) (X := (25000023137448795247/25000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013711133616605539/25000000000000000000 : ℝ) ≤ (200021767188843/200000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (25013711133616605539/25000000000000000000 : ℝ)^1024 ≤ (200021767188843/200000000000000 : ℝ)^5159 := by
      have hnat : (25013711133616605539 : ℕ)^1024*200000000000000^5159 ≤ 200021767188843^5159*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013711133616605539 25000000000000000000 200021767188843 200000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200021767188843/200000000000000 : ℝ)) (X := (25013711133616605539/25000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25027399129784415831/25000000000000000000 : ℝ) ≤ (5001087440940937/5000000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (25027399129784415831/25000000000000000000 : ℝ)^1024 ≤ (5001087440940937/5000000000000000 : ℝ)^5159 := by
      have hnat : (25027399129784415831 : ℕ)^1024*5000000000000000^5159 ≤ 5001087440940937^5159*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25027399129784415831 25000000000000000000 5001087440940937 5000000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001087440940937/5000000000000000 : ℝ)) (X := (25027399129784415831/25000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23137448795247/50000000000000000000 : ℝ) ≤ ((16995801645839176673/16997000000000000000 : ℝ)+2*(271630609931/424925000000000 : ℝ)*(5529/100000 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (16995801645839176673/16997000000000000000 : ℝ)+2*(271630609931/424925000000000 : ℝ)*(5529/100000 : ℝ)=(5000000918501213/5000000000000000 : ℝ) by norm_num, show 1+2*(23137448795247/50000000000000000000 : ℝ)=(25000023137448795247/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27399129784415831/50000000000000000000 : ℝ)+(23137448795247/50000000000000000000 : ℝ) ≤ ((16995801645839176673/16997000000000000000 : ℝ)+(271630609931/424925000000000 : ℝ)*((11263/50000 : ℝ)+(5529/100000 : ℝ)))^(5159/1024 : ℝ) := by
    rw [show (16995801645839176673/16997000000000000000 : ℝ)+(271630609931/424925000000000 : ℝ)*((11263/50000 : ℝ)+(5529/100000 : ℝ))=(200021767188843/200000000000000 : ℝ) by norm_num, show 1+(27399129784415831/50000000000000000000 : ℝ)+(23137448795247/50000000000000000000 : ℝ)=(25013711133616605539/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27399129784415831/50000000000000000000 : ℝ) ≤ ((16995801645839176673/16997000000000000000 : ℝ)+2*(271630609931/424925000000000 : ℝ)*(11263/50000 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (16995801645839176673/16997000000000000000 : ℝ)+2*(271630609931/424925000000000 : ℝ)*(11263/50000 : ℝ)=(5001087440940937/5000000000000000 : ℝ) by norm_num, show 1+2*(27399129784415831/50000000000000000000 : ℝ)=(25027399129784415831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16995801645839176673/16997000000000000000 : ℝ)*(X 1 0+X 2 0)+(271630609931/424925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (5529/100000 : ℝ)) (hi := (11263/50000 : ℝ)) (c := (16995801645839176673/16997000000000000000 : ℝ)) (alpha := (271630609931/424925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16995801645839176673/16997000000000000000 : ℝ)*(X 0 1+X 2 1)+(271630609931/424925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (5529/100000 : ℝ)) (hi := (11263/50000 : ℝ)) (c := (16995801645839176673/16997000000000000000 : ℝ)) (alpha := (271630609931/424925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16995801645839176673/16997000000000000000 : ℝ)*(X 0 2+X 1 2)+(271630609931/424925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (5529/100000 : ℝ)) (hi := (11263/50000 : ℝ)) (c := (16995801645839176673/16997000000000000000 : ℝ)) (alpha := (271630609931/424925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1470693629/10000000000 : ℝ)*X 0 0+(5502276799/10000000000 : ℝ)*X 0 1+(511821453/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677444977/5000000000 : ℝ)*X 1 0+(-52217731/312500000 : ℝ)*X 1 1+(5118214137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677444519/5000000000 : ℝ)*X 2 0+(5118214931/10000000000 : ℝ)*X 2 1+(-835483783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((824624449/2000000000 : ℝ)*X 0 0+(9027233/25000000 : ℝ)*X 0 1+(1170324613/2500000000 : ℝ)*X 0 2+(824624449/2000000000 : ℝ)*X 1 0+(9027233/25000000 : ℝ)*X 1 1+(1170324613/2500000000 : ℝ)*X 1 2+(824624449/2000000000 : ℝ)*X 2 0+(9027233/25000000 : ℝ)*X 2 1+(1170324613/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-735456639/5000000000 : ℝ)*X 0 0+(640358877/1250000000 : ℝ)*X 0 1+(2748771651/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050424121/2000000000 : ℝ)*X 1 0+(-1291637321/10000000000 : ℝ)*X 1 1+(1374385727/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((525211987/1000000000 : ℝ)*X 2 0+(5497543179/10000000000 : ℝ)*X 2 1+(-322909493/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4123735613/10000000000 : ℝ)*X 0 0+(4668321119/10000000000 : ℝ)*X 0 1+(906021513/2500000000 : ℝ)*X 0 2+(4123735613/10000000000 : ℝ)*X 1 0+(4668321119/10000000000 : ℝ)*X 1 1+(906021513/2500000000 : ℝ)*X 1 2+(4123735613/10000000000 : ℝ)*X 2 0+(4668321119/10000000000 : ℝ)*X 2 1+(906021513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4936230684383372409392847261/424925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (856039123/50000000000000 : ℝ)*(base19) + (632971909/50000000000000 : ℝ)*(base23) + (394731/100000000000000 : ℝ)*(lower2) + (58930299/20000000000000 : ℝ)*(upper3) + (2514211/2000000000000 : ℝ)*(upper5) + (884501784799881/50000000000000 : ℝ)*(major0) + (884501784799881/50000000000000 : ℝ)*(major1) + (884501784799881/50000000000000 : ℝ)*(major2) + (650939960731137/25000000000000 : ℝ)*(sp0) + (650942424795291/25000000000000 : ℝ)*(sp1) + (325471268164449/12500000000000 : ℝ)*(sp2) + (934230183251043/100000000000000 : ℝ)*(sp3) + (5784167431/50000000000000 : ℝ)*(sp4) + (5157465383/100000000000000 : ℝ)*(sp7) + (467117670358213/50000000000000 : ℝ)*(f.failure) + (260377141125941/10000000000000 : ℝ)*(f.sum) + (98193716027261/42492500000000000000000000000 : ℝ)*base66 + (2180614235090034087/849850000000000000000000000000000 : ℝ)*base68 + (8451054056254215913/849850000000000000000000000000000 : ℝ)*base69 + (556574189752315913/849850000000000000000000000000000 : ℝ)*base71 + (257593025915977/84985000000000000000000000000 : ℝ)*base74 + (3555545223659815913/849850000000000000000000000000000 : ℝ)*base75 + (2436303496141684087/849850000000000000000000000000000 : ℝ)*base78 + (6325209340486165913/849850000000000000000000000000000 : ℝ)*base79 + (25473996309993/5311562500000000000000000000 : ℝ)*base81 + (28347913/5000000000000000000000 : ℝ)*base90 + (28347913/5000000000000000000000 : ℝ)*base92 + (28347913/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (174853823988739130483618079/18475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (266029629/12500000000000 : ℝ)*(base19) + (1890809047/100000000000000 : ℝ)*(base23) + (55503919/50000000000000 : ℝ)*(upper3) + (102579753/100000000000000 : ℝ)*(lower4) + (91629813/100000000000000 : ℝ)*(upper5) + (1813317441899957/100000000000000 : ℝ)*(major0) + (1813317441899957/100000000000000 : ℝ)*(major1) + (1813317441899957/100000000000000 : ℝ)*(major2) + (1222658531/6250000000000 : ℝ)*(sp1) + (16535525587/100000000000000 : ℝ)*(sp2) + (1334498228260409/50000000000000 : ℝ)*(sp4) + (266897476574729/10000000000000 : ℝ)*(sp5) + (1334489015093091/50000000000000 : ℝ)*(sp6) + (95763811180083/10000000000000 : ℝ)*(sp7) + (95763811180083/10000000000000 : ℝ)*(f.failure) + (1334498228260409/50000000000000 : ℝ)*(f.sum) + (3302026259623/1847500000000000000000000000 : ℝ)*base65 + (68059700521312307/73900000000000000000000000000000 : ℝ)*base67 + (376248983943112307/73900000000000000000000000000000 : ℝ)*base69 + (9686787693912307/73900000000000000000000000000000 : ℝ)*base71 + (2933323286039/923750000000000000000000000 : ℝ)*base73 + (188783191297287693/73900000000000000000000000000000 : ℝ)*base76 + (567204644807112307/73900000000000000000000000000000 : ℝ)*base77 + (841254635582012307/73900000000000000000000000000000 : ℝ)*base79 + (3838407926893/1847500000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base88 + (6872783/1000000000000000000000 : ℝ)*base90 + (6872783/1000000000000000000000 : ℝ)*base92 + (6872783/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1693_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11263/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5529/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2207/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1693_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1693_s2_0 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1475696029/10000000000 : ℝ)*x 0 + (5482145547/10000000000 : ℝ)*x 1 + (1283753981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1475696029/10000000000 : ℝ)^5167 ≤ (9196084457517/100000000000000 : ℝ)^4143 := by
    have hnat : (1475696029 : ℕ)^5167*100000000000000^4143 ≤ 9196084457517^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475696029 10000000000 9196084457517 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482145547/10000000000 : ℝ)^5167 ≤ (9450582165211/20000000000000 : ℝ)^4143 := by
    have hnat : (5482145547 : ℕ)^5167*20000000000000^4143 ≤ 9450582165211^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482145547 10000000000 9450582165211 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1283753981/2500000000 : ℝ)^5167 ≤ (10887751175497/25000000000000 : ℝ)^4143 := by
    have hnat : (1283753981 : ℕ)^5167*25000000000000^4143 ≤ 10887751175497^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283753981 2500000000 10887751175497 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1475696029/10000000000 : ℝ), (5482145547/10000000000 : ℝ), (1283753981/2500000000 : ℝ)] ![(9196084457517/100000000000000 : ℝ), (9450582165211/20000000000000 : ℝ), (10887751175497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1475696029/10000000000 : ℝ)|^5167 ≤ (9196084457517/100000000000000 : ℝ)^4143
        have hw : |(-1475696029/10000000000 : ℝ)|=(1475696029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482145547/10000000000 : ℝ)|^5167 ≤ (9450582165211/20000000000000 : ℝ)^4143
        have hw : |(5482145547/10000000000 : ℝ)|=(5482145547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1283753981/2500000000 : ℝ)|^5167 ≤ (10887751175497/25000000000000 : ℝ)^4143
        have hw : |(1283753981/2500000000 : ℝ)|=(1283753981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s2_1 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668685389/1250000000 : ℝ)*x 0 + (-206999247/1250000000 : ℝ)*x 1 + (641876997/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668685389/1250000000 : ℝ)^5167 ≤ (9166220683649/20000000000000 : ℝ)^4143 := by
    have hnat : (668685389 : ℕ)^5167*20000000000000^4143 ≤ 9166220683649^4143*1250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668685389 1250000000 9166220683649 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206999247/1250000000 : ℝ)^5167 ≤ (2654472827379/25000000000000 : ℝ)^4143 := by
    have hnat : (206999247 : ℕ)^5167*25000000000000^4143 ≤ 2654472827379^4143*1250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206999247 1250000000 2654472827379 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641876997/1250000000 : ℝ)^5167 ≤ (21775502626007/50000000000000 : ℝ)^4143 := by
    have hnat : (641876997 : ℕ)^5167*50000000000000^4143 ≤ 21775502626007^4143*1250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641876997 1250000000 21775502626007 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668685389/1250000000 : ℝ), (-206999247/1250000000 : ℝ), (641876997/1250000000 : ℝ)] ![(9166220683649/20000000000000 : ℝ), (2654472827379/25000000000000 : ℝ), (21775502626007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668685389/1250000000 : ℝ)|^5167 ≤ (9166220683649/20000000000000 : ℝ)^4143
        have hw : |(668685389/1250000000 : ℝ)|=(668685389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-206999247/1250000000 : ℝ)|^5167 ≤ (2654472827379/25000000000000 : ℝ)^4143
        have hw : |(-206999247/1250000000 : ℝ)|=(206999247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641876997/1250000000 : ℝ)|^5167 ≤ (21775502626007/50000000000000 : ℝ)^4143
        have hw : |(641876997/1250000000 : ℝ)|=(641876997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s2_2 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674741599/5000000000 : ℝ)*x 0 + (1283753911/2500000000 : ℝ)*x 1 + (-1655994301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674741599/5000000000 : ℝ)^5167 ≤ (916622086743/2000000000000 : ℝ)^4143 := by
    have hnat : (2674741599 : ℕ)^5167*2000000000000^4143 ≤ 916622086743^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674741599 5000000000 916622086743 2000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283753911/2500000000 : ℝ)^5167 ≤ (43551001740309/100000000000000 : ℝ)^4143 := by
    have hnat : (1283753911 : ℕ)^5167*100000000000000^4143 ≤ 43551001740309^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283753911 2500000000 43551001740309 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1655994301/10000000000 : ℝ)^5167 ≤ (10617893908397/100000000000000 : ℝ)^4143 := by
    have hnat : (1655994301 : ℕ)^5167*100000000000000^4143 ≤ 10617893908397^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655994301 10000000000 10617893908397 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674741599/5000000000 : ℝ), (1283753911/2500000000 : ℝ), (-1655994301/10000000000 : ℝ)] ![(916622086743/2000000000000 : ℝ), (43551001740309/100000000000000 : ℝ), (10617893908397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674741599/5000000000 : ℝ)|^5167 ≤ (916622086743/2000000000000 : ℝ)^4143
        have hw : |(2674741599/5000000000 : ℝ)|=(2674741599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283753911/2500000000 : ℝ)|^5167 ≤ (43551001740309/100000000000000 : ℝ)^4143
        have hw : |(1283753911/2500000000 : ℝ)|=(1283753911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1655994301/10000000000 : ℝ)|^5167 ≤ (10617893908397/100000000000000 : ℝ)^4143
        have hw : |(-1655994301/10000000000 : ℝ)|=(1655994301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s2_3 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1031743617/2500000000 : ℝ)*x 0 + (146480139/400000000 : ℝ)*x 1 + (4629476561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031743617/2500000000 : ℝ)^5167 ≤ (33161169447637/100000000000000 : ℝ)^4143 := by
    have hnat : (1031743617 : ℕ)^5167*100000000000000^4143 ≤ 33161169447637^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031743617 2500000000 33161169447637 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146480139/400000000 : ℝ)^5167 ≤ (7142097752357/25000000000000 : ℝ)^4143 := by
    have hnat : (146480139 : ℕ)^5167*25000000000000^4143 ≤ 7142097752357^4143*400000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146480139 400000000 7142097752357 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4629476561/10000000000 : ℝ)^5167 ≤ (38270439530557/100000000000000 : ℝ)^4143 := by
    have hnat : (4629476561 : ℕ)^5167*100000000000000^4143 ≤ 38270439530557^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4629476561 10000000000 38270439530557 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1031743617/2500000000 : ℝ), (146480139/400000000 : ℝ), (4629476561/10000000000 : ℝ)] ![(33161169447637/100000000000000 : ℝ), (7142097752357/25000000000000 : ℝ), (38270439530557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1031743617/2500000000 : ℝ)|^5167 ≤ (33161169447637/100000000000000 : ℝ)^4143
        have hw : |(1031743617/2500000000 : ℝ)|=(1031743617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(146480139/400000000 : ℝ)|^5167 ≤ (7142097752357/25000000000000 : ℝ)^4143
        have hw : |(146480139/400000000 : ℝ)|=(146480139/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4629476561/10000000000 : ℝ)|^5167 ≤ (38270439530557/100000000000000 : ℝ)^4143
        have hw : |(4629476561/10000000000 : ℝ)|=(4629476561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s2_4 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-737929351/5000000000 : ℝ)*x 0 + (5138822727/10000000000 : ℝ)*x 1 + (2739140753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (737929351/5000000000 : ℝ)^5167 ≤ (4598674379959/50000000000000 : ℝ)^4143 := by
    have hnat : (737929351 : ℕ)^5167*50000000000000^4143 ≤ 4598674379959^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737929351 5000000000 4598674379959 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138822727/10000000000 : ℝ)^5167 ≤ (8718254911923/20000000000000 : ℝ)^4143 := by
    have hnat : (5138822727 : ℕ)^5167*20000000000000^4143 ≤ 8718254911923^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138822727 10000000000 8718254911923 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2739140753/5000000000 : ℝ)^5167 ≤ (11802844166757/25000000000000 : ℝ)^4143 := by
    have hnat : (2739140753 : ℕ)^5167*25000000000000^4143 ≤ 11802844166757^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739140753 5000000000 11802844166757 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-737929351/5000000000 : ℝ), (5138822727/10000000000 : ℝ), (2739140753/5000000000 : ℝ)] ![(4598674379959/50000000000000 : ℝ), (8718254911923/20000000000000 : ℝ), (11802844166757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-737929351/5000000000 : ℝ)|^5167 ≤ (4598674379959/50000000000000 : ℝ)^4143
        have hw : |(-737929351/5000000000 : ℝ)|=(737929351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138822727/10000000000 : ℝ)|^5167 ≤ (8718254911923/20000000000000 : ℝ)^4143
        have hw : |(5138822727/10000000000 : ℝ)|=(5138822727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2739140753/5000000000 : ℝ)|^5167 ≤ (11802844166757/25000000000000 : ℝ)^4143
        have hw : |(2739140753/5000000000 : ℝ)|=(2739140753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s2_5 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628324957/5000000000 : ℝ)*x 0 + (-1312728441/10000000000 : ℝ)*x 1 + (5478281597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628324957/5000000000 : ℝ)^5167 ≤ (44841323021911/100000000000000 : ℝ)^4143 := by
    have hnat : (2628324957 : ℕ)^5167*100000000000000^4143 ≤ 44841323021911^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628324957 5000000000 44841323021911 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1312728441/10000000000 : ℝ)^5167 ≤ (794729932411/10000000000000 : ℝ)^4143 := by
    have hnat : (1312728441 : ℕ)^5167*10000000000000^4143 ≤ 794729932411^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312728441 10000000000 794729932411 10000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5478281597/10000000000 : ℝ)^5167 ≤ (11802844411273/25000000000000 : ℝ)^4143 := by
    have hnat : (5478281597 : ℕ)^5167*25000000000000^4143 ≤ 11802844411273^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478281597 10000000000 11802844411273 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628324957/5000000000 : ℝ), (-1312728441/10000000000 : ℝ), (5478281597/10000000000 : ℝ)] ![(44841323021911/100000000000000 : ℝ), (794729932411/10000000000000 : ℝ), (11802844411273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628324957/5000000000 : ℝ)|^5167 ≤ (44841323021911/100000000000000 : ℝ)^4143
        have hw : |(2628324957/5000000000 : ℝ)|=(2628324957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1312728441/10000000000 : ℝ)|^5167 ≤ (794729932411/10000000000000 : ℝ)^4143
        have hw : |(-1312728441/10000000000 : ℝ)|=(1312728441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5478281597/10000000000 : ℝ)|^5167 ≤ (11802844411273/25000000000000 : ℝ)^4143
        have hw : |(5478281597/10000000000 : ℝ)|=(5478281597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s2_6 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628324957/5000000000 : ℝ)*x 0 + (5478281607/10000000000 : ℝ)*x 1 + (-656364213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628324957/5000000000 : ℝ)^5167 ≤ (44841323021911/100000000000000 : ℝ)^4143 := by
    have hnat : (2628324957 : ℕ)^5167*100000000000000^4143 ≤ 44841323021911^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628324957 5000000000 44841323021911 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478281607/10000000000 : ℝ)^5167 ≤ (11802844438143/25000000000000 : ℝ)^4143 := by
    have hnat : (5478281607 : ℕ)^5167*25000000000000^4143 ≤ 11802844438143^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478281607 10000000000 11802844438143 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656364213/5000000000 : ℝ)^5167 ≤ (1589459842171/20000000000000 : ℝ)^4143 := by
    have hnat : (656364213 : ℕ)^5167*20000000000000^4143 ≤ 1589459842171^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656364213 5000000000 1589459842171 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628324957/5000000000 : ℝ), (5478281607/10000000000 : ℝ), (-656364213/5000000000 : ℝ)] ![(44841323021911/100000000000000 : ℝ), (11802844438143/25000000000000 : ℝ), (1589459842171/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628324957/5000000000 : ℝ)|^5167 ≤ (44841323021911/100000000000000 : ℝ)^4143
        have hw : |(2628324957/5000000000 : ℝ)|=(2628324957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478281607/10000000000 : ℝ)|^5167 ≤ (11802844438143/25000000000000 : ℝ)^4143
        have hw : |(5478281607/10000000000 : ℝ)|=(5478281607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-656364213/5000000000 : ℝ)|^5167 ≤ (1589459842171/20000000000000 : ℝ)^4143
        have hw : |(-656364213/5000000000 : ℝ)|=(656364213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s2_7 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (825485527/2000000000 : ℝ)*x 0 + (4618865891/10000000000 : ℝ)*x 1 + (1836386633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825485527/2000000000 : ℝ)^5167 ≤ (33165710805791/100000000000000 : ℝ)^4143 := by
    have hnat : (825485527 : ℕ)^5167*100000000000000^4143 ≤ 33165710805791^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825485527 2000000000 33165710805791 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4618865891/10000000000 : ℝ)^5167 ≤ (9540268856873/25000000000000 : ℝ)^4143 := by
    have hnat : (4618865891 : ℕ)^5167*25000000000000^4143 ≤ 9540268856873^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4618865891 10000000000 9540268856873 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1836386633/5000000000 : ℝ)^5167 ≤ (14336606877627/50000000000000 : ℝ)^4143 := by
    have hnat : (1836386633 : ℕ)^5167*50000000000000^4143 ≤ 14336606877627^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836386633 5000000000 14336606877627 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(825485527/2000000000 : ℝ), (4618865891/10000000000 : ℝ), (1836386633/5000000000 : ℝ)] ![(33165710805791/100000000000000 : ℝ), (9540268856873/25000000000000 : ℝ), (14336606877627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(825485527/2000000000 : ℝ)|^5167 ≤ (33165710805791/100000000000000 : ℝ)^4143
        have hw : |(825485527/2000000000 : ℝ)|=(825485527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4618865891/10000000000 : ℝ)|^5167 ≤ (9540268856873/25000000000000 : ℝ)^4143
        have hw : |(4618865891/10000000000 : ℝ)|=(4618865891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1836386633/5000000000 : ℝ)|^5167 ≤ (14336606877627/50000000000000 : ℝ)^4143
        have hw : |(1836386633/5000000000 : ℝ)|=(1836386633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1693_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2207/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9843/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8617/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2207/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2207/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2207/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2207/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2207/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2207/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9477/100000 : ℝ) ^ (5159/1024 : ℝ) ≤ (139768707764799/20000000000000000000 : ℝ) := by
    have hpowers : (9477/100000 : ℝ)^5159 ≤ (139768707764799/20000000000000000000 : ℝ)^1024 := by
      have hnat : (9477 : ℕ)^5159*20000000000000000000^1024 ≤ 139768707764799^1024*100000^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9477 100000 139768707764799 20000000000000000000 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9477/100000 : ℝ)) (X := (139768707764799/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2207/12500 : ℝ) ^ (5159/1024 : ℝ) ≤ (16061229534632701/100000000000000000000 : ℝ) := by
    have hpowers : (2207/12500 : ℝ)^5159 ≤ (16061229534632701/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2207 : ℕ)^5159*100000000000000000000^1024 ≤ 16061229534632701^1024*12500^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2207 12500 16061229534632701 100000000000000000000 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2207/12500 : ℝ)) (X := (16061229534632701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000139768707764799/10000000000000000000 : ℝ) ≤ (625001733891683/625000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (10000139768707764799/10000000000000000000 : ℝ)^1024 ≤ (625001733891683/625000000000000 : ℝ)^5159 := by
      have hnat : (10000139768707764799 : ℕ)^1024*625000000000000^5159 ≤ 625001733891683^5159*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000139768707764799 10000000000000000000 625001733891683 625000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625001733891683/625000000000000 : ℝ)) (X := (10000139768707764799/10000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502095009134182087/12500000000000000000 : ℝ) ≤ (10000332645128943/10000000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (12502095009134182087/12500000000000000000 : ℝ)^1024 ≤ (10000332645128943/10000000000000000 : ℝ)^5159 := by
      have hnat : (12502095009134182087 : ℕ)^1024*10000000000000000^5159 ≤ 10000332645128943^5159*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502095009134182087 12500000000000000000 10000332645128943 10000000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000332645128943/10000000000000000 : ℝ)) (X := (12502095009134182087/12500000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016061229534632701/50000000000000000000 : ℝ) ≤ (5000318773995479/5000000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (50016061229534632701/50000000000000000000 : ℝ)^1024 ≤ (5000318773995479/5000000000000000 : ℝ)^5159 := by
      have hnat : (50016061229534632701 : ℕ)^1024*5000000000000000^5159 ≤ 5000318773995479^5159*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016061229534632701 50000000000000000000 5000318773995479 5000000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000318773995479/5000000000000000 : ℝ)) (X := (50016061229534632701/50000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(139768707764799/20000000000000000000 : ℝ) ≤ ((40892223887577285901/40895000000000000000 : ℝ)+2*(60980572403/163580000000000 : ℝ)*(9477/100000 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (40892223887577285901/40895000000000000000 : ℝ)+2*(60980572403/163580000000000 : ℝ)*(9477/100000 : ℝ)=(625001733891683/625000000000000 : ℝ) by norm_num, show 1+2*(139768707764799/20000000000000000000 : ℝ)=(10000139768707764799/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16061229534632701/100000000000000000000 : ℝ)+(139768707764799/20000000000000000000 : ℝ) ≤ ((40892223887577285901/40895000000000000000 : ℝ)+(60980572403/163580000000000 : ℝ)*((2207/12500 : ℝ)+(9477/100000 : ℝ)))^(5159/1024 : ℝ) := by
    rw [show (40892223887577285901/40895000000000000000 : ℝ)+(60980572403/163580000000000 : ℝ)*((2207/12500 : ℝ)+(9477/100000 : ℝ))=(10000332645128943/10000000000000000 : ℝ) by norm_num, show 1+(16061229534632701/100000000000000000000 : ℝ)+(139768707764799/20000000000000000000 : ℝ)=(12502095009134182087/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16061229534632701/100000000000000000000 : ℝ) ≤ ((40892223887577285901/40895000000000000000 : ℝ)+2*(60980572403/163580000000000 : ℝ)*(2207/12500 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (40892223887577285901/40895000000000000000 : ℝ)+2*(60980572403/163580000000000 : ℝ)*(2207/12500 : ℝ)=(5000318773995479/5000000000000000 : ℝ) by norm_num, show 1+2*(16061229534632701/100000000000000000000 : ℝ)=(50016061229534632701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40892223887577285901/40895000000000000000 : ℝ)*(X 1 0+X 2 0)+(60980572403/163580000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (9477/100000 : ℝ)) (hi := (2207/12500 : ℝ)) (c := (40892223887577285901/40895000000000000000 : ℝ)) (alpha := (60980572403/163580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40892223887577285901/40895000000000000000 : ℝ)*(X 0 1+X 2 1)+(60980572403/163580000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (9477/100000 : ℝ)) (hi := (2207/12500 : ℝ)) (c := (40892223887577285901/40895000000000000000 : ℝ)) (alpha := (60980572403/163580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40892223887577285901/40895000000000000000 : ℝ)*(X 0 2+X 1 2)+(60980572403/163580000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (9477/100000 : ℝ)) (hi := (2207/12500 : ℝ)) (c := (40892223887577285901/40895000000000000000 : ℝ)) (alpha := (60980572403/163580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1475696029/10000000000 : ℝ)*X 0 0+(5482145547/10000000000 : ℝ)*X 0 1+(1283753981/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668685389/1250000000 : ℝ)*X 1 0+(-206999247/1250000000 : ℝ)*X 1 1+(641876997/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674741599/5000000000 : ℝ)*X 2 0+(1283753911/2500000000 : ℝ)*X 2 1+(-1655994301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1031743617/2500000000 : ℝ)*X 0 0+(146480139/400000000 : ℝ)*X 0 1+(4629476561/10000000000 : ℝ)*X 0 2+(1031743617/2500000000 : ℝ)*X 1 0+(146480139/400000000 : ℝ)*X 1 1+(4629476561/10000000000 : ℝ)*X 1 2+(1031743617/2500000000 : ℝ)*X 2 0+(146480139/400000000 : ℝ)*X 2 1+(4629476561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-737929351/5000000000 : ℝ)*X 0 0+(5138822727/10000000000 : ℝ)*X 0 1+(2739140753/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628324957/5000000000 : ℝ)*X 1 0+(-1312728441/10000000000 : ℝ)*X 1 1+(5478281597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2628324957/5000000000 : ℝ)*X 2 0+(5478281607/10000000000 : ℝ)*X 2 1+(-656364213/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((825485527/2000000000 : ℝ)*X 0 0+(4618865891/10000000000 : ℝ)*X 0 1+(1836386633/5000000000 : ℝ)*X 0 2+(825485527/2000000000 : ℝ)*X 1 0+(4618865891/10000000000 : ℝ)*X 1 1+(1836386633/5000000000 : ℝ)*X 1 2+(825485527/2000000000 : ℝ)*X 2 0+(4618865891/10000000000 : ℝ)*X 2 1+(1836386633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4989278437071170350929/1022375000000000000000000000 : ℝ) := by norm_num
    linear_combination (557358511/100000000000000 : ℝ)*(base19) + (664979703/100000000000000 : ℝ)*(base23) + (10210007/50000000000000 : ℝ)*(lower2) + (18549589/12500000000000 : ℝ)*(upper3) + (26608547/50000000000000 : ℝ)*(lower4) + (978601316341789/50000000000000 : ℝ)*(major0) + (978601316341789/50000000000000 : ℝ)*(major1) + (978601316341789/50000000000000 : ℝ)*(major2) + (144038760590399/5000000000000 : ℝ)*(sp0) + (144038933350461/5000000000000 : ℝ)*(sp1) + (720194639847007/25000000000000 : ℝ)*(sp2) + (1033622771976451/100000000000000 : ℝ)*(sp3) + (501569969/12500000000000 : ℝ)*(sp4) + (3106353419/100000000000000 : ℝ)*(sp7) + (103362587832987/10000000000000 : ℝ)*(f.failure) + (2880779224367731/100000000000000 : ℝ)*(f.sum) + (22743494054123/8179000000000000000000000000 : ℝ)*base65 + (11725827942551933111/2044750000000000000000000000000000 : ℝ)*base68 + (18401393155062183111/2044750000000000000000000000000000 : ℝ)*base70 + (6227828595086816889/2044750000000000000000000000000000 : ℝ)*base71 + (615428261/255593750000000000000000000 : ℝ)*base74 + (6938214797649816889/2044750000000000000000000000000000 : ℝ)*base75 + (8105993438367183111/2044750000000000000000000000000000 : ℝ)*base78 + (7807339054705066889/2044750000000000000000000000000000 : ℝ)*base79 + (39685334411689/8179000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2876713/1000000000000000000000 : ℝ)*base89 + (2876713/1000000000000000000000 : ℝ)*base91 + (2876713/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4180193810762306021525294349/1022375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (461345439/100000000000000 : ℝ)*(base19) + (113921901/20000000000000 : ℝ)*(base23) + (82647801/100000000000000 : ℝ)*(upper3) + (754769/1562500000000 : ℝ)*(lower4) + (42728413/50000000000000 : ℝ)*(upper5) + (1000711049339917/50000000000000 : ℝ)*(major0) + (1000711049339917/50000000000000 : ℝ)*(major1) + (1000711049339917/50000000000000 : ℝ)*(major2) + (4450401673/100000000000000 : ℝ)*(sp1) + (5377372559/100000000000000 : ℝ)*(sp2) + (1472932634467331/50000000000000 : ℝ)*(sp4) + (58917207143751/2000000000000 : ℝ)*(sp5) + (1472929660976299/50000000000000 : ℝ)*(sp6) + (528489396067353/50000000000000 : ℝ)*(sp7) + (528489396067353/50000000000000 : ℝ)*(f.failure) + (1472932634467331/50000000000000 : ℝ)*(f.sum) + (1169611460099/1022375000000000000000000000 : ℝ)*base66 + (1231287475758360217/2044750000000000000000000000000000 : ℝ)*base67 + (3478496531789639783/2044750000000000000000000000000000 : ℝ)*base70 + (4978003406054860217/2044750000000000000000000000000000 : ℝ)*base71 + (1501193457789/817900000000000000000000000 : ℝ)*base74 + (2333328647096860217/2044750000000000000000000000000000 : ℝ)*base75 + (2879838037839360217/2044750000000000000000000000000000 : ℝ)*base77 + (8720336373424639783/2044750000000000000000000000000000 : ℝ)*base80 + (17419432560129/8179000000000000000000000000 : ℝ)*base82 + (3276947/5000000000000000000000 : ℝ)*base89 + (3276947/5000000000000000000000 : ℝ)*base91 + (3276947/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1693_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2207/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8617/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1693_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1693_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8617/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1693_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1693_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1693_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8617/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1693_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
