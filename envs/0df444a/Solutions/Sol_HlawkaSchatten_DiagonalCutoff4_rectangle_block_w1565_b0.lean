-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1565_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:25:21.585761+00:00
-- url     : https://prove2.me/submissions/c55a2899-a3bb-4265-ae52-52a472c34545

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
theorem support_rectangle_w1565_s0_0 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-407758951/2500000000 : ℝ)*x 0 + (5873171029/10000000000 : ℝ)*x 1 + (1219335117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407758951/2500000000 : ℝ)^4627 ≤ (9741809456199/100000000000000 : ℝ)^3603 := by
    have hnat : (407758951 : ℕ)^4627*100000000000000^3603 ≤ 9741809456199^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407758951 2500000000 9741809456199 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5873171029/10000000000 : ℝ)^4627 ≤ (50487573299007/100000000000000 : ℝ)^3603 := by
    have hnat : (5873171029 : ℕ)^4627*100000000000000^3603 ≤ 50487573299007^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5873171029 10000000000 50487573299007 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1219335117/2500000000 : ℝ)^4627 ≤ (39770617223177/100000000000000 : ℝ)^3603 := by
    have hnat : (1219335117 : ℕ)^4627*100000000000000^3603 ≤ 39770617223177^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1219335117 2500000000 39770617223177 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-407758951/2500000000 : ℝ), (5873171029/10000000000 : ℝ), (1219335117/2500000000 : ℝ)] ![(9741809456199/100000000000000 : ℝ), (50487573299007/100000000000000 : ℝ), (39770617223177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-407758951/2500000000 : ℝ)|^4627 ≤ (9741809456199/100000000000000 : ℝ)^3603
        have hw : |(-407758951/2500000000 : ℝ)|=(407758951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5873171029/10000000000 : ℝ)|^4627 ≤ (50487573299007/100000000000000 : ℝ)^3603
        have hw : |(5873171029/10000000000 : ℝ)|=(5873171029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1219335117/2500000000 : ℝ)|^4627 ≤ (39770617223177/100000000000000 : ℝ)^3603
        have hw : |(1219335117/2500000000 : ℝ)|=(1219335117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s0_1 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273327303/500000000 : ℝ)*x 0 + (-2185530881/10000000000 : ℝ)*x 1 + (4877340471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273327303/500000000 : ℝ)^4627 ≤ (46043576958761/100000000000000 : ℝ)^3603 := by
    have hnat : (273327303 : ℕ)^4627*100000000000000^3603 ≤ 46043576958761^3603*500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273327303 500000000 46043576958761 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185530881/10000000000 : ℝ)^4627 ≤ (3546451442489/25000000000000 : ℝ)^3603 := by
    have hnat : (2185530881 : ℕ)^4627*25000000000000^3603 ≤ 3546451442489^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185530881 10000000000 3546451442489 25000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4877340471/10000000000 : ℝ)^4627 ≤ (621415894603/1562500000000 : ℝ)^3603 := by
    have hnat : (4877340471 : ℕ)^4627*1562500000000^3603 ≤ 621415894603^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4877340471 10000000000 621415894603 1562500000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273327303/500000000 : ℝ), (-2185530881/10000000000 : ℝ), (4877340471/10000000000 : ℝ)] ![(46043576958761/100000000000000 : ℝ), (3546451442489/25000000000000 : ℝ), (621415894603/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273327303/500000000 : ℝ)|^4627 ≤ (46043576958761/100000000000000 : ℝ)^3603
        have hw : |(273327303/500000000 : ℝ)|=(273327303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2185530881/10000000000 : ℝ)|^4627 ≤ (3546451442489/25000000000000 : ℝ)^3603
        have hw : |(-2185530881/10000000000 : ℝ)|=(2185530881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4877340471/10000000000 : ℝ)|^4627 ≤ (621415894603/1562500000000 : ℝ)^3603
        have hw : |(4877340471/10000000000 : ℝ)|=(4877340471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s0_2 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5466546111/10000000000 : ℝ)*x 0 + (1219335103/2500000000 : ℝ)*x 1 + (-2185530889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5466546111/10000000000 : ℝ)^4627 ≤ (5755447188801/12500000000000 : ℝ)^3603 := by
    have hnat : (5466546111 : ℕ)^4627*12500000000000^3603 ≤ 5755447188801^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466546111 10000000000 5755447188801 12500000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1219335103/2500000000 : ℝ)^4627 ≤ (19885308318383/50000000000000 : ℝ)^3603 := by
    have hnat : (1219335103 : ℕ)^4627*50000000000000^3603 ≤ 19885308318383^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1219335103 2500000000 19885308318383 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185530889/10000000000 : ℝ)^4627 ≤ (88661286479/625000000000 : ℝ)^3603 := by
    have hnat : (2185530889 : ℕ)^4627*625000000000^3603 ≤ 88661286479^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185530889 10000000000 88661286479 625000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5466546111/10000000000 : ℝ), (1219335103/2500000000 : ℝ), (-2185530889/10000000000 : ℝ)] ![(5755447188801/12500000000000 : ℝ), (19885308318383/50000000000000 : ℝ), (88661286479/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5466546111/10000000000 : ℝ)|^4627 ≤ (5755447188801/12500000000000 : ℝ)^3603
        have hw : |(5466546111/10000000000 : ℝ)|=(5466546111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1219335103/2500000000 : ℝ)|^4627 ≤ (19885308318383/50000000000000 : ℝ)^3603
        have hw : |(1219335103/2500000000 : ℝ)|=(1219335103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185530889/10000000000 : ℝ)|^4627 ≤ (88661286479/625000000000 : ℝ)^3603
        have hw : |(-2185530889/10000000000 : ℝ)|=(2185530889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s0_3 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2065571587/5000000000 : ℝ)*x 0 + (61857821/200000000 : ℝ)*x 1 + (271780299/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065571587/5000000000 : ℝ)^4627 ≤ (32133238027939/100000000000000 : ℝ)^3603 := by
    have hnat : (2065571587 : ℕ)^4627*100000000000000^3603 ≤ 32133238027939^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065571587 5000000000 32133238027939 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61857821/200000000 : ℝ)^4627 ≤ (22157582331869/100000000000000 : ℝ)^3603 := by
    have hnat : (61857821 : ℕ)^4627*100000000000000^3603 ≤ 22157582331869^3603*200000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61857821 200000000 22157582331869 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271780299/500000000 : ℝ)^4627 ≤ (45709179630173/100000000000000 : ℝ)^3603 := by
    have hnat : (271780299 : ℕ)^4627*100000000000000^3603 ≤ 45709179630173^3603*500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271780299 500000000 45709179630173 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2065571587/5000000000 : ℝ), (61857821/200000000 : ℝ), (271780299/500000000 : ℝ)] ![(32133238027939/100000000000000 : ℝ), (22157582331869/100000000000000 : ℝ), (45709179630173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2065571587/5000000000 : ℝ)|^4627 ≤ (32133238027939/100000000000000 : ℝ)^3603
        have hw : |(2065571587/5000000000 : ℝ)|=(2065571587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(61857821/200000000 : ℝ)|^4627 ≤ (22157582331869/100000000000000 : ℝ)^3603
        have hw : |(61857821/200000000 : ℝ)|=(61857821/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271780299/500000000 : ℝ)|^4627 ≤ (45709179630173/100000000000000 : ℝ)^3603
        have hw : |(271780299/500000000 : ℝ)|=(271780299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s0_4 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1634128499/10000000000 : ℝ)*x 0 + (4902464771/10000000000 : ℝ)*x 1 + (1461788939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1634128499/10000000000 : ℝ)^4627 ≤ (9765537690279/100000000000000 : ℝ)^3603 := by
    have hnat : (1634128499 : ℕ)^4627*100000000000000^3603 ≤ 9765537690279^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634128499 10000000000 9765537690279 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4902464771/10000000000 : ℝ)^4627 ≤ (40033902103497/100000000000000 : ℝ)^3603 := by
    have hnat : (4902464771 : ℕ)^4627*100000000000000^3603 ≤ 40033902103497^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4902464771 10000000000 40033902103497 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1461788939/2500000000 : ℝ)^4627 ≤ (10040112038227/20000000000000 : ℝ)^3603 := by
    have hnat : (1461788939 : ℕ)^4627*20000000000000^3603 ≤ 10040112038227^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461788939 2500000000 10040112038227 20000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1634128499/10000000000 : ℝ), (4902464771/10000000000 : ℝ), (1461788939/2500000000 : ℝ)] ![(9765537690279/100000000000000 : ℝ), (40033902103497/100000000000000 : ℝ), (10040112038227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1634128499/10000000000 : ℝ)|^4627 ≤ (9765537690279/100000000000000 : ℝ)^3603
        have hw : |(-1634128499/10000000000 : ℝ)|=(1634128499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4902464771/10000000000 : ℝ)|^4627 ≤ (40033902103497/100000000000000 : ℝ)^3603
        have hw : |(4902464771/10000000000 : ℝ)|=(4902464771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1461788939/2500000000 : ℝ)|^4627 ≤ (10040112038227/20000000000000 : ℝ)^3603
        have hw : |(1461788939/2500000000 : ℝ)|=(1461788939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s0_5 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194319299/10000000000 : ℝ)*x 0 + (-1215716001/10000000000 : ℝ)*x 1 + (5847154821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194319299/10000000000 : ℝ)^4627 ≤ (43120096034801/100000000000000 : ℝ)^3603 := by
    have hnat : (5194319299 : ℕ)^4627*100000000000000^3603 ≤ 43120096034801^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194319299 10000000000 43120096034801 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1215716001/10000000000 : ℝ)^4627 ≤ (6679354061917/100000000000000 : ℝ)^3603 := by
    have hnat : (1215716001 : ℕ)^4627*100000000000000^3603 ≤ 6679354061917^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215716001 10000000000 6679354061917 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5847154821/10000000000 : ℝ)^4627 ≤ (50200549882273/100000000000000 : ℝ)^3603 := by
    have hnat : (5847154821 : ℕ)^4627*100000000000000^3603 ≤ 50200549882273^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5847154821 10000000000 50200549882273 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194319299/10000000000 : ℝ), (-1215716001/10000000000 : ℝ), (5847154821/10000000000 : ℝ)] ![(43120096034801/100000000000000 : ℝ), (6679354061917/100000000000000 : ℝ), (50200549882273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194319299/10000000000 : ℝ)|^4627 ≤ (43120096034801/100000000000000 : ℝ)^3603
        have hw : |(5194319299/10000000000 : ℝ)|=(5194319299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1215716001/10000000000 : ℝ)|^4627 ≤ (6679354061917/100000000000000 : ℝ)^3603
        have hw : |(-1215716001/10000000000 : ℝ)|=(1215716001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5847154821/10000000000 : ℝ)|^4627 ≤ (50200549882273/100000000000000 : ℝ)^3603
        have hw : |(5847154821/10000000000 : ℝ)|=(5847154821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s0_6 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194317961/10000000000 : ℝ)*x 0 + (2923578299/5000000000 : ℝ)*x 1 + (-1215715247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194317961/10000000000 : ℝ)^4627 ≤ (21560040885383/50000000000000 : ℝ)^3603 := by
    have hnat : (5194317961 : ℕ)^4627*50000000000000^3603 ≤ 21560040885383^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194317961 10000000000 21560040885383 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2923578299/5000000000 : ℝ)^4627 ≤ (784383898041/1562500000000 : ℝ)^3603 := by
    have hnat : (2923578299 : ℕ)^4627*1562500000000^3603 ≤ 784383898041^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2923578299 5000000000 784383898041 1562500000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1215715247/10000000000 : ℝ)^4627 ≤ (6679348741951/100000000000000 : ℝ)^3603 := by
    have hnat : (1215715247 : ℕ)^4627*100000000000000^3603 ≤ 6679348741951^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215715247 10000000000 6679348741951 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194317961/10000000000 : ℝ), (2923578299/5000000000 : ℝ), (-1215715247/10000000000 : ℝ)] ![(21560040885383/50000000000000 : ℝ), (784383898041/1562500000000 : ℝ), (6679348741951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194317961/10000000000 : ℝ)|^4627 ≤ (21560040885383/50000000000000 : ℝ)^3603
        have hw : |(5194317961/10000000000 : ℝ)|=(5194317961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2923578299/5000000000 : ℝ)|^4627 ≤ (784383898041/1562500000000 : ℝ)^3603
        have hw : |(2923578299/5000000000 : ℝ)|=(2923578299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1215715247/10000000000 : ℝ)|^4627 ≤ (6679348741951/100000000000000 : ℝ)^3603
        have hw : |(-1215715247/10000000000 : ℝ)|=(1215715247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s0_7 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4138415169/10000000000 : ℝ)*x 0 + (5376500113/10000000000 : ℝ)*x 1 + (3154093829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4138415169/10000000000 : ℝ)^4627 ≤ (32205895725277/100000000000000 : ℝ)^3603 := by
    have hnat : (4138415169 : ℕ)^4627*100000000000000^3603 ≤ 32205895725277^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138415169 10000000000 32205895725277 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376500113/10000000000 : ℝ)^4627 ≤ (22535936864243/50000000000000 : ℝ)^3603 := by
    have hnat : (5376500113 : ℕ)^4627*50000000000000^3603 ≤ 22535936864243^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376500113 10000000000 22535936864243 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154093829/10000000000 : ℝ)^4627 ≤ (11361115261789/50000000000000 : ℝ)^3603 := by
    have hnat : (3154093829 : ℕ)^4627*50000000000000^3603 ≤ 11361115261789^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154093829 10000000000 11361115261789 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4138415169/10000000000 : ℝ), (5376500113/10000000000 : ℝ), (3154093829/10000000000 : ℝ)] ![(32205895725277/100000000000000 : ℝ), (22535936864243/50000000000000 : ℝ), (11361115261789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4138415169/10000000000 : ℝ)|^4627 ≤ (32205895725277/100000000000000 : ℝ)^3603
        have hw : |(4138415169/10000000000 : ℝ)|=(4138415169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376500113/10000000000 : ℝ)|^4627 ≤ (22535936864243/50000000000000 : ℝ)^3603
        have hw : |(5376500113/10000000000 : ℝ)|=(5376500113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154093829/10000000000 : ℝ)|^4627 ≤ (11361115261789/50000000000000 : ℝ)^3603
        have hw : |(3154093829/10000000000 : ℝ)|=(3154093829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1565_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (697/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1551/6250 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4625/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4625 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4625*1^1024 ≤ 0^1024*1^4625 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4625 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4625/1024 : ℝ) ≤ (797321617978114423/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4625 ≤ (797321617978114423/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4625*50000000000000000000^1024 ≤ 797321617978114423^1024*5^4625 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 797321617978114423 50000000000000000000 4625 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (797321617978114423/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4625 := by
      have hnat : (1 : ℕ)^1024*1^4625 ≤ 1^4625*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50797321617978114423/50000000000000000000 : ℝ) ≤ (10035089134800147/10000000000000000 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (50797321617978114423/50000000000000000000 : ℝ)^1024 ≤ (10035089134800147/10000000000000000 : ℝ)^4625 := by
      have hnat : (50797321617978114423 : ℕ)^1024*10000000000000000^4625 ≤ 10035089134800147^4625*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50797321617978114423 50000000000000000000 10035089134800147 10000000000000000 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10035089134800147/10000000000000000 : ℝ)) (X := (50797321617978114423/50000000000000000000 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25797321617978114423/25000000000000000000 : ℝ) ≤ (5035089134800147/5000000000000000 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (25797321617978114423/25000000000000000000 : ℝ)^1024 ≤ (5035089134800147/5000000000000000 : ℝ)^4625 := by
      have hnat : (25797321617978114423 : ℕ)^1024*5000000000000000^4625 ≤ 5035089134800147^4625*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25797321617978114423 25000000000000000000 5035089134800147 5000000000000000 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5035089134800147/5000000000000000 : ℝ)) (X := (25797321617978114423/25000000000000000000 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(35089134800147/4000000000000000 : ℝ)*(0 : ℝ))^(4625/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35089134800147/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(797321617978114423/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(35089134800147/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4625/1024 : ℝ) := by
    rw [show (1 : ℝ)+(35089134800147/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10035089134800147/10000000000000000 : ℝ) by norm_num, show 1+(797321617978114423/50000000000000000000 : ℝ)+(0 : ℝ)=(50797321617978114423/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(797321617978114423/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(35089134800147/4000000000000000 : ℝ)*(2/5 : ℝ))^(4625/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35089134800147/4000000000000000 : ℝ)*(2/5 : ℝ)=(5035089134800147/5000000000000000 : ℝ) by norm_num, show 1+2*(797321617978114423/50000000000000000000 : ℝ)=(25797321617978114423/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(35089134800147/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35089134800147/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(35089134800147/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35089134800147/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(35089134800147/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35089134800147/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-407758951/2500000000 : ℝ)*X 0 0+(5873171029/10000000000 : ℝ)*X 0 1+(1219335117/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((273327303/500000000 : ℝ)*X 1 0+(-2185530881/10000000000 : ℝ)*X 1 1+(4877340471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5466546111/10000000000 : ℝ)*X 2 0+(1219335103/2500000000 : ℝ)*X 2 1+(-2185530889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2065571587/5000000000 : ℝ)*X 0 0+(61857821/200000000 : ℝ)*X 0 1+(271780299/500000000 : ℝ)*X 0 2+(2065571587/5000000000 : ℝ)*X 1 0+(61857821/200000000 : ℝ)*X 1 1+(271780299/500000000 : ℝ)*X 1 2+(2065571587/5000000000 : ℝ)*X 2 0+(61857821/200000000 : ℝ)*X 2 1+(271780299/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1634128499/10000000000 : ℝ)*X 0 0+(4902464771/10000000000 : ℝ)*X 0 1+(1461788939/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5194319299/10000000000 : ℝ)*X 1 0+(-1215716001/10000000000 : ℝ)*X 1 1+(5847154821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5194317961/10000000000 : ℝ)*X 2 0+(2923578299/5000000000 : ℝ)*X 2 1+(-1215715247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4138415169/10000000000 : ℝ)*X 0 0+(5376500113/10000000000 : ℝ)*X 0 1+(3154093829/10000000000 : ℝ)*X 0 2+(4138415169/10000000000 : ℝ)*X 1 0+(5376500113/10000000000 : ℝ)*X 1 1+(3154093829/10000000000 : ℝ)*X 1 2+(4138415169/10000000000 : ℝ)*X 2 0+(5376500113/10000000000 : ℝ)*X 2 1+(3154093829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (226982409414266073620193/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8604891/20000000000000 : ℝ)*(base1) + (935587841/100000000000000 : ℝ)*(base19) + (94495643/10000000000000 : ℝ)*(base23) + (60477707/50000000000000 : ℝ)*(upper3) + (7572073/6250000000000 : ℝ)*(upper5) + (715525938331927/100000000000000 : ℝ)*(major0) + (715525938331927/100000000000000 : ℝ)*(major1) + (715525938331927/100000000000000 : ℝ)*(major2) + (251047546333291/25000000000000 : ℝ)*(sp0) + (1004192688117313/100000000000000 : ℝ)*(sp1) + (251048169687181/25000000000000 : ℝ)*(sp2) + (2667853614977/625000000000 : ℝ)*(sp3) + (870349111/25000000000000 : ℝ)*(sp4) + (148021631/10000000000000 : ℝ)*(sp7) + (213429050818543/50000000000000 : ℝ)*(f.failure) + (502096811852577/50000000000000 : ℝ)*(f.sum) + (190026762793269/200000000000000000000000000000 : ℝ)*base65 + (5226856050393269/400000000000000000000000000000 : ℝ)*base67 + (2635816891993269/400000000000000000000000000000 : ℝ)*base69 + (2600814554393269/400000000000000000000000000000 : ℝ)*base71 + (626332438993269/200000000000000000000000000000 : ℝ)*base73 + (956432089193269/400000000000000000000000000000 : ℝ)*base75 + (1268624320793269/400000000000000000000000000000 : ℝ)*base77 + (3208354367193269/400000000000000000000000000000 : ℝ)*base79 + (261402096406731/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (6053587/2500000000000000000000 : ℝ)*base90 + (6053587/2500000000000000000000 : ℝ)*base92 + (6053587/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (208850209408629503903781/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1338080109/100000000000000 : ℝ)*(base19) + (842915527/50000000000000 : ℝ)*(base23) + (687072127/100000000000000 : ℝ)*(base39) + (1385753/12500000000000 : ℝ)*(upper3) + (120879897/25000000000000 : ℝ)*(upper5) + (188563199020291/25000000000000 : ℝ)*(major0) + (188563199020291/25000000000000 : ℝ)*(major1) + (188563027252259/25000000000000 : ℝ)*(major2) + (1148735631/25000000000000 : ℝ)*(sp1) + (708909367/20000000000000 : ℝ)*(sp2) + (4134935222869/390625000000 : ℝ)*(sp4) + (1058537484031831/100000000000000 : ℝ)*(sp5) + (1058538873748701/100000000000000 : ℝ)*(sp6) + (449961209568779/100000000000000 : ℝ)*(sp7) + (449961209568779/100000000000000 : ℝ)*(f.failure) + (1058544104126591/100000000000000 : ℝ)*(f.sum) + (3511221811297/2000000000000000000000000000 : ℝ)*base65 + (1176114542182073/100000000000000000000000000000 : ℝ)*base67 + (796181474717223/100000000000000000000000000000 : ℝ)*base70 + (552953463282073/100000000000000000000000000000 : ℝ)*base71 + (14095578937297/2000000000000000000000000000 : ℝ)*base73 + (559191601817223/100000000000000000000000000000 : ℝ)*base76 + (1128250883082777/100000000000000000000000000000 : ℝ)*base77 + (1178319758282777/100000000000000000000000000000 : ℝ)*base79 + (179532233667223/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (54914111/5000000000000000000000 : ℝ)*base90 + (54914111/5000000000000000000000 : ℝ)*base92 + (4914111/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1565_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (697/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1551/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1565_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1565_s1_0 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1770905089/10000000000 : ℝ)*x 0 + (5537695711/10000000000 : ℝ)*x 1 + (512268679/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1770905089/10000000000 : ℝ)^4627 ≤ (10827462017979/100000000000000 : ℝ)^3603 := by
    have hnat : (1770905089 : ℕ)^4627*100000000000000^3603 ≤ 10827462017979^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770905089 10000000000 10827462017979 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5537695711/10000000000 : ℝ)^4627 ≤ (23407297095891/50000000000000 : ℝ)^3603 := by
    have hnat : (5537695711 : ℕ)^4627*50000000000000^3603 ≤ 23407297095891^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5537695711 10000000000 23407297095891 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512268679/1000000000 : ℝ)^4627 ≤ (42357943782511/100000000000000 : ℝ)^3603 := by
    have hnat : (512268679 : ℕ)^4627*100000000000000^3603 ≤ 42357943782511^3603*1000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512268679 1000000000 42357943782511 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1770905089/10000000000 : ℝ), (5537695711/10000000000 : ℝ), (512268679/1000000000 : ℝ)] ![(10827462017979/100000000000000 : ℝ), (23407297095891/50000000000000 : ℝ), (42357943782511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1770905089/10000000000 : ℝ)|^4627 ≤ (10827462017979/100000000000000 : ℝ)^3603
        have hw : |(-1770905089/10000000000 : ℝ)|=(1770905089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5537695711/10000000000 : ℝ)|^4627 ≤ (23407297095891/50000000000000 : ℝ)^3603
        have hw : |(5537695711/10000000000 : ℝ)|=(5537695711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512268679/1000000000 : ℝ)|^4627 ≤ (42357943782511/100000000000000 : ℝ)^3603
        have hw : |(512268679/1000000000 : ℝ)|=(512268679/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s1_1 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075457461/2000000000 : ℝ)*x 0 + (-198809889/1000000000 : ℝ)*x 1 + (128067167/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075457461/2000000000 : ℝ)^4627 ≤ (9016069711319/20000000000000 : ℝ)^3603 := by
    have hnat : (1075457461 : ℕ)^4627*20000000000000^3603 ≤ 9016069711319^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075457461 2000000000 9016069711319 20000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198809889/1000000000 : ℝ)^4627 ≤ (3140427205599/25000000000000 : ℝ)^3603 := by
    have hnat : (198809889 : ℕ)^4627*25000000000000^3603 ≤ 3140427205599^3603*1000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198809889 1000000000 3140427205599 25000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128067167/250000000 : ℝ)^4627 ≤ (10589485653613/25000000000000 : ℝ)^3603 := by
    have hnat : (128067167 : ℕ)^4627*25000000000000^3603 ≤ 10589485653613^3603*250000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128067167 250000000 10589485653613 25000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075457461/2000000000 : ℝ), (-198809889/1000000000 : ℝ), (128067167/250000000 : ℝ)] ![(9016069711319/20000000000000 : ℝ), (3140427205599/25000000000000 : ℝ), (10589485653613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075457461/2000000000 : ℝ)|^4627 ≤ (9016069711319/20000000000000 : ℝ)^3603
        have hw : |(1075457461/2000000000 : ℝ)|=(1075457461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198809889/1000000000 : ℝ)|^4627 ≤ (3140427205599/25000000000000 : ℝ)^3603
        have hw : |(-198809889/1000000000 : ℝ)|=(198809889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128067167/250000000 : ℝ)|^4627 ≤ (10589485653613/25000000000000 : ℝ)^3603
        have hw : |(128067167/250000000 : ℝ)|=(128067167/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s1_2 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377287209/10000000000 : ℝ)*x 0 + (1024537429/2000000000 : ℝ)*x 1 + (-248512301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377287209/10000000000 : ℝ)^4627 ≤ (5635043440381/12500000000000 : ℝ)^3603 := by
    have hnat : (5377287209 : ℕ)^4627*12500000000000^3603 ≤ 5635043440381^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377287209 10000000000 5635043440381 12500000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024537429/2000000000 : ℝ)^4627 ≤ (21178973776079/50000000000000 : ℝ)^3603 := by
    have hnat : (1024537429 : ℕ)^4627*50000000000000^3603 ≤ 21178973776079^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024537429 2000000000 21178973776079 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248512301/1250000000 : ℝ)^4627 ≤ (12561704911349/100000000000000 : ℝ)^3603 := by
    have hnat : (248512301 : ℕ)^4627*100000000000000^3603 ≤ 12561704911349^3603*1250000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248512301 1250000000 12561704911349 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377287209/10000000000 : ℝ), (1024537429/2000000000 : ℝ), (-248512301/1250000000 : ℝ)] ![(5635043440381/12500000000000 : ℝ), (21178973776079/50000000000000 : ℝ), (12561704911349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377287209/10000000000 : ℝ)|^4627 ≤ (5635043440381/12500000000000 : ℝ)^3603
        have hw : |(5377287209/10000000000 : ℝ)|=(5377287209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1024537429/2000000000 : ℝ)|^4627 ≤ (21178973776079/50000000000000 : ℝ)^3603
        have hw : |(1024537429/2000000000 : ℝ)|=(1024537429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-248512301/1250000000 : ℝ)|^4627 ≤ (12561704911349/100000000000000 : ℝ)^3603
        have hw : |(-248512301/1250000000 : ℝ)|=(248512301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s1_3 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (846055889/2000000000 : ℝ)*x 0 + (3764913913/10000000000 : ℝ)*x 1 + (948246677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (846055889/2000000000 : ℝ)^4627 ≤ (33126862243043/100000000000000 : ℝ)^3603 := by
    have hnat : (846055889 : ℕ)^4627*100000000000000^3603 ≤ 33126862243043^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846055889 2000000000 33126862243043 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3764913913/10000000000 : ℝ)^4627 ≤ (71305235393/250000000000 : ℝ)^3603 := by
    have hnat : (3764913913 : ℕ)^4627*250000000000^3603 ≤ 71305235393^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3764913913 10000000000 71305235393 250000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948246677/2000000000 : ℝ)^4627 ≤ (599235055847/1562500000000 : ℝ)^3603 := by
    have hnat : (948246677 : ℕ)^4627*1562500000000^3603 ≤ 599235055847^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948246677 2000000000 599235055847 1562500000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(846055889/2000000000 : ℝ), (3764913913/10000000000 : ℝ), (948246677/2000000000 : ℝ)] ![(33126862243043/100000000000000 : ℝ), (71305235393/250000000000 : ℝ), (599235055847/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(846055889/2000000000 : ℝ)|^4627 ≤ (33126862243043/100000000000000 : ℝ)^3603
        have hw : |(846055889/2000000000 : ℝ)|=(846055889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3764913913/10000000000 : ℝ)|^4627 ≤ (71305235393/250000000000 : ℝ)^3603
        have hw : |(3764913913/10000000000 : ℝ)|=(3764913913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(948246677/2000000000 : ℝ)|^4627 ≤ (599235055847/1562500000000 : ℝ)^3603
        have hw : |(948246677/2000000000 : ℝ)|=(948246677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s1_4 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-885561413/5000000000 : ℝ)*x 0 + (1281749461/2500000000 : ℝ)*x 1 + (276666029/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (885561413/5000000000 : ℝ)^4627 ≤ (10829171664957/100000000000000 : ℝ)^3603 := by
    have hnat : (885561413 : ℕ)^4627*100000000000000^3603 ≤ 10829171664957^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885561413 5000000000 10829171664957 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1281749461/2500000000 : ℝ)^4627 ≤ (42403727145463/100000000000000 : ℝ)^3603 := by
    have hnat : (1281749461 : ℕ)^4627*100000000000000^3603 ≤ 42403727145463^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281749461 2500000000 42403727145463 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276666029/500000000 : ℝ)^4627 ≤ (45670997247/97656250000 : ℝ)^3603 := by
    have hnat : (276666029 : ℕ)^4627*97656250000^3603 ≤ 45670997247^3603*500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276666029 500000000 45670997247 97656250000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-885561413/5000000000 : ℝ), (1281749461/2500000000 : ℝ), (276666029/500000000 : ℝ)] ![(10829171664957/100000000000000 : ℝ), (42403727145463/100000000000000 : ℝ), (45670997247/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-885561413/5000000000 : ℝ)|^4627 ≤ (10829171664957/100000000000000 : ℝ)^3603
        have hw : |(-885561413/5000000000 : ℝ)|=(885561413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1281749461/2500000000 : ℝ)|^4627 ≤ (42403727145463/100000000000000 : ℝ)^3603
        have hw : |(1281749461/2500000000 : ℝ)|=(1281749461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276666029/500000000 : ℝ)|^4627 ≤ (45670997247/97656250000 : ℝ)^3603
        have hw : |(276666029/500000000 : ℝ)|=(276666029/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s1_5 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053467209/2000000000 : ℝ)*x 0 + (-1577464851/10000000000 : ℝ)*x 1 + (1383330241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053467209/2000000000 : ℝ)^4627 ≤ (2195002822857/5000000000000 : ℝ)^3603 := by
    have hnat : (1053467209 : ℕ)^4627*5000000000000^3603 ≤ 2195002822857^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053467209 2000000000 2195002822857 5000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1577464851/10000000000 : ℝ)^4627 ≤ (4666419092251/50000000000000 : ℝ)^3603 := by
    have hnat : (1577464851 : ℕ)^4627*50000000000000^3603 ≤ 4666419092251^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577464851 10000000000 4666419092251 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1383330241/2500000000 : ℝ)^4627 ≤ (182684005269/390625000000 : ℝ)^3603 := by
    have hnat : (1383330241 : ℕ)^4627*390625000000^3603 ≤ 182684005269^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383330241 2500000000 182684005269 390625000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053467209/2000000000 : ℝ), (-1577464851/10000000000 : ℝ), (1383330241/2500000000 : ℝ)] ![(2195002822857/5000000000000 : ℝ), (4666419092251/50000000000000 : ℝ), (182684005269/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053467209/2000000000 : ℝ)|^4627 ≤ (2195002822857/5000000000000 : ℝ)^3603
        have hw : |(1053467209/2000000000 : ℝ)|=(1053467209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1577464851/10000000000 : ℝ)|^4627 ≤ (4666419092251/50000000000000 : ℝ)^3603
        have hw : |(-1577464851/10000000000 : ℝ)|=(1577464851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1383330241/2500000000 : ℝ)|^4627 ≤ (182684005269/390625000000 : ℝ)^3603
        have hw : |(1383330241/2500000000 : ℝ)|=(1383330241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s1_6 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316833907/2500000000 : ℝ)*x 0 + (5533321113/10000000000 : ℝ)*x 1 + (-63098609/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316833907/2500000000 : ℝ)^4627 ≤ (878001039879/2000000000000 : ℝ)^3603 := by
    have hnat : (1316833907 : ℕ)^4627*2000000000000^3603 ≤ 878001039879^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316833907 2500000000 878001039879 2000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5533321113/10000000000 : ℝ)^4627 ≤ (4676710696611/10000000000000 : ℝ)^3603 := by
    have hnat : (5533321113 : ℕ)^4627*10000000000000^3603 ≤ 4676710696611^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5533321113 10000000000 4676710696611 10000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63098609/400000000 : ℝ)^4627 ≤ (1166605128261/12500000000000 : ℝ)^3603 := by
    have hnat : (63098609 : ℕ)^4627*12500000000000^3603 ≤ 1166605128261^3603*400000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63098609 400000000 1166605128261 12500000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316833907/2500000000 : ℝ), (5533321113/10000000000 : ℝ), (-63098609/400000000 : ℝ)] ![(878001039879/2000000000000 : ℝ), (4676710696611/10000000000000 : ℝ), (1166605128261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316833907/2500000000 : ℝ)|^4627 ≤ (878001039879/2000000000000 : ℝ)^3603
        have hw : |(1316833907/2500000000 : ℝ)|=(1316833907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5533321113/10000000000 : ℝ)|^4627 ≤ (4676710696611/10000000000000 : ℝ)^3603
        have hw : |(5533321113/10000000000 : ℝ)|=(5533321113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63098609/400000000 : ℝ)|^4627 ≤ (1166605128261/12500000000000 : ℝ)^3603
        have hw : |(-63098609/400000000 : ℝ)|=(63098609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s1_7 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8461581/20000000 : ℝ)*x 0 + (2365545933/5000000000 : ℝ)*x 1 + (1887603353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8461581/20000000 : ℝ)^4627 ≤ (33132001751429/100000000000000 : ℝ)^3603 := by
    have hnat : (8461581 : ℕ)^4627*100000000000000^3603 ≤ 33132001751429^3603*20000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8461581 20000000 33132001751429 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2365545933/5000000000 : ℝ)^4627 ≤ (19122864072463/50000000000000 : ℝ)^3603 := by
    have hnat : (2365545933 : ℕ)^4627*50000000000000^3603 ≤ 19122864072463^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2365545933 5000000000 19122864072463 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1887603353/5000000000 : ℝ)^4627 ≤ (28622270094139/100000000000000 : ℝ)^3603 := by
    have hnat : (1887603353 : ℕ)^4627*100000000000000^3603 ≤ 28622270094139^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887603353 5000000000 28622270094139 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8461581/20000000 : ℝ), (2365545933/5000000000 : ℝ), (1887603353/5000000000 : ℝ)] ![(33132001751429/100000000000000 : ℝ), (19122864072463/50000000000000 : ℝ), (28622270094139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8461581/20000000 : ℝ)|^4627 ≤ (33132001751429/100000000000000 : ℝ)^3603
        have hw : |(8461581/20000000 : ℝ)|=(8461581/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2365545933/5000000000 : ℝ)|^4627 ≤ (19122864072463/50000000000000 : ℝ)^3603
        have hw : |(2365545933/5000000000 : ℝ)|=(2365545933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1887603353/5000000000 : ℝ)|^4627 ≤ (28622270094139/100000000000000 : ℝ)^3603
        have hw : |(1887603353/5000000000 : ℝ)|=(1887603353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1565_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1551/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9013/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17801/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1551/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (697/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1551/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (697/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1551/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (697/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1551/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (697/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1551/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (697/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1551/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (697/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (697/20000 : ℝ) ^ (4625/1024 : ℝ) ≤ (26044187261903/100000000000000000000 : ℝ) := by
    have hpowers : (697/20000 : ℝ)^4625 ≤ (26044187261903/100000000000000000000 : ℝ)^1024 := by
      have hnat : (697 : ℕ)^4625*100000000000000000000^1024 ≤ 26044187261903^1024*20000^4625 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        697 20000 26044187261903 100000000000000000000 4625 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (697/20000 : ℝ)) (X := (26044187261903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1551/6250 : ℝ) ^ (4625/1024 : ℝ) ≤ (18460549065068247/10000000000000000000 : ℝ) := by
    have hpowers : (1551/6250 : ℝ)^4625 ≤ (18460549065068247/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1551 : ℕ)^4625*10000000000000000000^1024 ≤ 18460549065068247^1024*6250^4625 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1551 6250 18460549065068247 10000000000000000000 4625 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1551/6250 : ℝ)) (X := (18460549065068247/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000026044187261903/50000000000000000000 : ℝ) ≤ (5000000576632267/5000000000000000 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (50000026044187261903/50000000000000000000 : ℝ)^1024 ≤ (5000000576632267/5000000000000000 : ℝ)^4625 := by
      have hnat : (50000026044187261903 : ℕ)^1024*5000000000000000^4625 ≤ 5000000576632267^4625*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000026044187261903 50000000000000000000 5000000576632267 5000000000000000 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000576632267/5000000000000000 : ℝ)) (X := (50000026044187261903/50000000000000000000 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100184631534837944373/100000000000000000000 : ℝ) ≤ (10004084906994129/10000000000000000 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (100184631534837944373/100000000000000000000 : ℝ)^1024 ≤ (10004084906994129/10000000000000000 : ℝ)^4625 := by
      have hnat : (100184631534837944373 : ℕ)^1024*10000000000000000^4625 ≤ 10004084906994129^4625*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100184631534837944373 100000000000000000000 10004084906994129 10000000000000000 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004084906994129/10000000000000000 : ℝ)) (X := (100184631534837944373/100000000000000000000 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5018460549065068247/5000000000000000000 : ℝ) ≤ (2502042165180931/2500000000000000 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (5018460549065068247/5000000000000000000 : ℝ)^1024 ≤ (2502042165180931/2500000000000000 : ℝ)^4625 := by
      have hnat : (5018460549065068247 : ℕ)^1024*2500000000000000^4625 ≤ 2502042165180931^4625*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5018460549065068247 5000000000000000000 2502042165180931 2500000000000000 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502042165180931/2500000000000000 : ℝ)) (X := (5018460549065068247/5000000000000000000 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(26044187261903/100000000000000000000 : ℝ) ≤ ((53320390209197624401/53327500000000000000 : ℝ)+2*(816750745919/426620000000000 : ℝ)*(697/20000 : ℝ))^(4625/1024 : ℝ) := by
    rw [show (53320390209197624401/53327500000000000000 : ℝ)+2*(816750745919/426620000000000 : ℝ)*(697/20000 : ℝ)=(5000000576632267/5000000000000000 : ℝ) by norm_num, show 1+2*(26044187261903/100000000000000000000 : ℝ)=(50000026044187261903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18460549065068247/10000000000000000000 : ℝ)+(26044187261903/100000000000000000000 : ℝ) ≤ ((53320390209197624401/53327500000000000000 : ℝ)+(816750745919/426620000000000 : ℝ)*((1551/6250 : ℝ)+(697/20000 : ℝ)))^(4625/1024 : ℝ) := by
    rw [show (53320390209197624401/53327500000000000000 : ℝ)+(816750745919/426620000000000 : ℝ)*((1551/6250 : ℝ)+(697/20000 : ℝ))=(10004084906994129/10000000000000000 : ℝ) by norm_num, show 1+(18460549065068247/10000000000000000000 : ℝ)+(26044187261903/100000000000000000000 : ℝ)=(100184631534837944373/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18460549065068247/10000000000000000000 : ℝ) ≤ ((53320390209197624401/53327500000000000000 : ℝ)+2*(816750745919/426620000000000 : ℝ)*(1551/6250 : ℝ))^(4625/1024 : ℝ) := by
    rw [show (53320390209197624401/53327500000000000000 : ℝ)+2*(816750745919/426620000000000 : ℝ)*(1551/6250 : ℝ)=(2502042165180931/2500000000000000 : ℝ) by norm_num, show 1+2*(18460549065068247/10000000000000000000 : ℝ)=(5018460549065068247/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (53320390209197624401/53327500000000000000 : ℝ)*(X 1 0+X 2 0)+(816750745919/426620000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (697/20000 : ℝ)) (hi := (1551/6250 : ℝ)) (c := (53320390209197624401/53327500000000000000 : ℝ)) (alpha := (816750745919/426620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (53320390209197624401/53327500000000000000 : ℝ)*(X 0 1+X 2 1)+(816750745919/426620000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (697/20000 : ℝ)) (hi := (1551/6250 : ℝ)) (c := (53320390209197624401/53327500000000000000 : ℝ)) (alpha := (816750745919/426620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (53320390209197624401/53327500000000000000 : ℝ)*(X 0 2+X 1 2)+(816750745919/426620000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (697/20000 : ℝ)) (hi := (1551/6250 : ℝ)) (c := (53320390209197624401/53327500000000000000 : ℝ)) (alpha := (816750745919/426620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1770905089/10000000000 : ℝ)*X 0 0+(5537695711/10000000000 : ℝ)*X 0 1+(512268679/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075457461/2000000000 : ℝ)*X 1 0+(-198809889/1000000000 : ℝ)*X 1 1+(128067167/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5377287209/10000000000 : ℝ)*X 2 0+(1024537429/2000000000 : ℝ)*X 2 1+(-248512301/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((846055889/2000000000 : ℝ)*X 0 0+(3764913913/10000000000 : ℝ)*X 0 1+(948246677/2000000000 : ℝ)*X 0 2+(846055889/2000000000 : ℝ)*X 1 0+(3764913913/10000000000 : ℝ)*X 1 1+(948246677/2000000000 : ℝ)*X 1 2+(846055889/2000000000 : ℝ)*X 2 0+(3764913913/10000000000 : ℝ)*X 2 1+(948246677/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-885561413/5000000000 : ℝ)*X 0 0+(1281749461/2500000000 : ℝ)*X 0 1+(276666029/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053467209/2000000000 : ℝ)*X 1 0+(-1577464851/10000000000 : ℝ)*X 1 1+(1383330241/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1316833907/2500000000 : ℝ)*X 2 0+(5533321113/10000000000 : ℝ)*X 2 1+(-63098609/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((8461581/20000000 : ℝ)*X 0 0+(2365545933/5000000000 : ℝ)*X 0 1+(1887603353/5000000000 : ℝ)*X 0 2+(8461581/20000000 : ℝ)*X 1 0+(2365545933/5000000000 : ℝ)*X 1 1+(1887603353/5000000000 : ℝ)*X 1 2+(8461581/20000000 : ℝ)*X 2 0+(2365545933/5000000000 : ℝ)*X 2 1+(1887603353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121277853982895388734577243/53327500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19859437/25000000000000 : ℝ)*(base1) + (201395059/25000000000000 : ℝ)*(base19) + (784913977/100000000000000 : ℝ)*(base23) + (165226623/100000000000000 : ℝ)*(upper5) + (34338646203273/2000000000000 : ℝ)*(major0) + (34338646203273/2000000000000 : ℝ)*(major1) + (34338646203273/2000000000000 : ℝ)*(major2) + (2409592986970059/100000000000000 : ℝ)*(sp0) + (301200004222587/12500000000000 : ℝ)*(sp1) + (602400286899417/25000000000000 : ℝ)*(sp2) + (1024259181901457/100000000000000 : ℝ)*(sp3) + (4512489667/50000000000000 : ℝ)*(sp4) + (1093150713/100000000000000 : ℝ)*(sp5) + (3350669491/100000000000000 : ℝ)*(sp7) + (128032826501087/12500000000000 : ℝ)*(f.failure) + (1204800966255823/50000000000000 : ℝ)*(f.sum) + (128979813921/66659375000000000000000000 : ℝ)*base65 + (763272916098479473/106655000000000000000000000000000 : ℝ)*base67 + (81186607022484473/106655000000000000000000000000000 : ℝ)*base69 + (578600110176089473/106655000000000000000000000000000 : ℝ)*base71 + (52326780937293/10665500000000000000000000000 : ℝ)*base73 + (909569349335774473/106655000000000000000000000000000 : ℝ)*base75 + (551145593662304473/106655000000000000000000000000000 : ℝ)*base77 + (835445819723654473/106655000000000000000000000000000 : ℝ)*base79 + (19512564725793/21331000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3829917/625000000000000000000 : ℝ)*base89 + (3829917/625000000000000000000 : ℝ)*base91 + (3829917/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15630812219774596210963802727/2666375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (515142081/50000000000000 : ℝ)*(base19) + (923363297/100000000000000 : ℝ)*(base23) + (13364859/25000000000000 : ℝ)*(upper2) + (102299457/50000000000000 : ℝ)*(upper3) + (4919509/5000000000000 : ℝ)*(upper5) + (1753623021386309/100000000000000 : ℝ)*(major0) + (1753623021386309/100000000000000 : ℝ)*(major1) + (1753623021386309/100000000000000 : ℝ)*(major2) + (8525883183/100000000000000 : ℝ)*(sp1) + (7875514531/100000000000000 : ℝ)*(sp2) + (1230547411115947/50000000000000 : ℝ)*(sp4) + (49221705321291/2000000000000 : ℝ)*(sp5) + (1230543011677033/50000000000000 : ℝ)*(sp6) + (523075512567097/50000000000000 : ℝ)*(sp7) + (523075512567097/50000000000000 : ℝ)*(f.failure) + (1230547411115947/50000000000000 : ℝ)*(f.sum) + (21783315780213/4266200000000000000000000000 : ℝ)*base66 + (9436655618192100909/5332750000000000000000000000000000 : ℝ)*base67 + (14109467110923899091/5332750000000000000000000000000000 : ℝ)*base70 + (8337672235376649091/5332750000000000000000000000000000 : ℝ)*base72 + (14674754554167/21331000000000000000000000000 : ℝ)*base73 + (59329854563353899091/5332750000000000000000000000000000 : ℝ)*base76 + (10309727782207149091/5332750000000000000000000000000000 : ℝ)*base78 + (15406333722560350909/5332750000000000000000000000000000 : ℝ)*base79 + (967285779611/853240000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (19466827/2500000000000000000000 : ℝ)*base89 + (19466827/2500000000000000000000 : ℝ)*base91 + (19466827/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1565_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1551/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9013/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17801/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1565_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1565_s2_0 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1789958281/10000000000 : ℝ)*x 0 + (68034009/125000000 : ℝ)*x 1 + (5205252031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1789958281/10000000000 : ℝ)^4627 ≤ (10977291112351/100000000000000 : ℝ)^3603 := by
    have hnat : (1789958281 : ℕ)^4627*100000000000000^3603 ≤ 10977291112351^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789958281 10000000000 10977291112351 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68034009/125000000 : ℝ)^4627 ≤ (9157205451993/20000000000000 : ℝ)^3603 := by
    have hnat : (68034009 : ℕ)^4627*20000000000000^3603 ≤ 9157205451993^3603*125000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68034009 125000000 9157205451993 20000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5205252031/10000000000 : ℝ)^4627 ≤ (43236681611713/100000000000000 : ℝ)^3603 := by
    have hnat : (5205252031 : ℕ)^4627*100000000000000^3603 ≤ 43236681611713^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205252031 10000000000 43236681611713 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1789958281/10000000000 : ℝ), (68034009/125000000 : ℝ), (5205252031/10000000000 : ℝ)] ![(10977291112351/100000000000000 : ℝ), (9157205451993/20000000000000 : ℝ), (43236681611713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1789958281/10000000000 : ℝ)|^4627 ≤ (10977291112351/100000000000000 : ℝ)^3603
        have hw : |(-1789958281/10000000000 : ℝ)|=(1789958281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68034009/125000000 : ℝ)|^4627 ≤ (9157205451993/20000000000000 : ℝ)^3603
        have hw : |(68034009/125000000 : ℝ)|=(68034009/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5205252031/10000000000 : ℝ)|^4627 ≤ (43236681611713/100000000000000 : ℝ)^3603
        have hw : |(5205252031/10000000000 : ℝ)|=(5205252031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s2_1 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352788699/10000000000 : ℝ)*x 0 + (-1911867399/10000000000 : ℝ)*x 1 + (5205252143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352788699/10000000000 : ℝ)^4627 ≤ (44816764542363/100000000000000 : ℝ)^3603 := by
    have hnat : (5352788699 : ℕ)^4627*100000000000000^3603 ≤ 44816764542363^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352788699 10000000000 44816764542363 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1911867399/10000000000 : ℝ)^4627 ≤ (5973276318313/50000000000000 : ℝ)^3603 := by
    have hnat : (1911867399 : ℕ)^4627*50000000000000^3603 ≤ 5973276318313^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911867399 10000000000 5973276318313 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5205252143/10000000000 : ℝ)^4627 ≤ (21618341403213/50000000000000 : ℝ)^3603 := by
    have hnat : (5205252143 : ℕ)^4627*50000000000000^3603 ≤ 21618341403213^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205252143 10000000000 21618341403213 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352788699/10000000000 : ℝ), (-1911867399/10000000000 : ℝ), (5205252143/10000000000 : ℝ)] ![(44816764542363/100000000000000 : ℝ), (5973276318313/50000000000000 : ℝ), (21618341403213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352788699/10000000000 : ℝ)|^4627 ≤ (44816764542363/100000000000000 : ℝ)^3603
        have hw : |(5352788699/10000000000 : ℝ)|=(5352788699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1911867399/10000000000 : ℝ)|^4627 ≤ (5973276318313/50000000000000 : ℝ)^3603
        have hw : |(-1911867399/10000000000 : ℝ)|=(1911867399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5205252143/10000000000 : ℝ)|^4627 ≤ (21618341403213/50000000000000 : ℝ)^3603
        have hw : |(5205252143/10000000000 : ℝ)|=(5205252143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s2_2 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676394281/5000000000 : ℝ)*x 0 + (5205252279/10000000000 : ℝ)*x 1 + (-1911867401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676394281/5000000000 : ℝ)^4627 ≤ (22408381534659/50000000000000 : ℝ)^3603 := by
    have hnat : (2676394281 : ℕ)^4627*50000000000000^3603 ≤ 22408381534659^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676394281 5000000000 22408381534659 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205252279/10000000000 : ℝ)^4627 ≤ (864733685143/2000000000000 : ℝ)^3603 := by
    have hnat : (5205252279 : ℕ)^4627*2000000000000^3603 ≤ 864733685143^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205252279 10000000000 864733685143 2000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1911867401/10000000000 : ℝ)^4627 ≤ (477862106107/4000000000000 : ℝ)^3603 := by
    have hnat : (1911867401 : ℕ)^4627*4000000000000^3603 ≤ 477862106107^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911867401 10000000000 477862106107 4000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676394281/5000000000 : ℝ), (5205252279/10000000000 : ℝ), (-1911867401/10000000000 : ℝ)] ![(22408381534659/50000000000000 : ℝ), (864733685143/2000000000000 : ℝ), (477862106107/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676394281/5000000000 : ℝ)|^4627 ≤ (22408381534659/50000000000000 : ℝ)^3603
        have hw : |(2676394281/5000000000 : ℝ)|=(2676394281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205252279/10000000000 : ℝ)|^4627 ≤ (864733685143/2000000000000 : ℝ)^3603
        have hw : |(5205252279/10000000000 : ℝ)|=(5205252279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1911867401/10000000000 : ℝ)|^4627 ≤ (477862106107/4000000000000 : ℝ)^3603
        have hw : |(-1911867401/10000000000 : ℝ)|=(1911867401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s2_3 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4244077057/10000000000 : ℝ)*x 0 + (1986110597/5000000000 : ℝ)*x 1 + (4530871319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244077057/10000000000 : ℝ)^4627 ≤ (33265682069883/100000000000000 : ℝ)^3603 := by
    have hnat : (4244077057 : ℕ)^4627*100000000000000^3603 ≤ 33265682069883^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244077057 10000000000 33265682069883 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1986110597/5000000000 : ℝ)^4627 ≤ (7638633670611/25000000000000 : ℝ)^3603 := by
    have hnat : (1986110597 : ℕ)^4627*25000000000000^3603 ≤ 7638633670611^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986110597 5000000000 7638633670611 25000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530871319/10000000000 : ℝ)^4627 ≤ (36179783225471/100000000000000 : ℝ)^3603 := by
    have hnat : (4530871319 : ℕ)^4627*100000000000000^3603 ≤ 36179783225471^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530871319 10000000000 36179783225471 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244077057/10000000000 : ℝ), (1986110597/5000000000 : ℝ), (4530871319/10000000000 : ℝ)] ![(33265682069883/100000000000000 : ℝ), (7638633670611/25000000000000 : ℝ), (36179783225471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244077057/10000000000 : ℝ)|^4627 ≤ (33265682069883/100000000000000 : ℝ)^3603
        have hw : |(4244077057/10000000000 : ℝ)|=(4244077057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1986110597/5000000000 : ℝ)|^4627 ≤ (7638633670611/25000000000000 : ℝ)^3603
        have hw : |(1986110597/5000000000 : ℝ)|=(1986110597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530871319/10000000000 : ℝ)|^4627 ≤ (36179783225471/100000000000000 : ℝ)^3603
        have hw : |(4530871319/10000000000 : ℝ)|=(4530871319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s2_4 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1789998723/10000000000 : ℝ)*x 0 + (520667187/1000000000 : ℝ)*x 1 + (5441289179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1789998723/10000000000 : ℝ)^4627 ≤ (548880481061/5000000000000 : ℝ)^3603 := by
    have hnat : (1789998723 : ℕ)^4627*5000000000000^3603 ≤ 548880481061^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789998723 10000000000 548880481061 5000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520667187/1000000000 : ℝ)^4627 ≤ (2703239234039/6250000000000 : ℝ)^3603 := by
    have hnat : (520667187 : ℕ)^4627*6250000000000^3603 ≤ 2703239234039^3603*1000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520667187 1000000000 2703239234039 6250000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441289179/10000000000 : ℝ)^4627 ≤ (45770562623789/100000000000000 : ℝ)^3603 := by
    have hnat : (5441289179 : ℕ)^4627*100000000000000^3603 ≤ 45770562623789^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441289179 10000000000 45770562623789 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1789998723/10000000000 : ℝ), (520667187/1000000000 : ℝ), (5441289179/10000000000 : ℝ)] ![(548880481061/5000000000000 : ℝ), (2703239234039/6250000000000 : ℝ), (45770562623789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1789998723/10000000000 : ℝ)|^4627 ≤ (548880481061/5000000000000 : ℝ)^3603
        have hw : |(-1789998723/10000000000 : ℝ)|=(1789998723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520667187/1000000000 : ℝ)|^4627 ≤ (2703239234039/6250000000000 : ℝ)^3603
        have hw : |(520667187/1000000000 : ℝ)|=(520667187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441289179/10000000000 : ℝ)|^4627 ≤ (45770562623789/100000000000000 : ℝ)^3603
        have hw : |(5441289179/10000000000 : ℝ)|=(5441289179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s2_5 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289992311/10000000000 : ℝ)*x 0 + (-209478857/1250000000 : ℝ)*x 1 + (2720644973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289992311/10000000000 : ℝ)^4627 ≤ (44142696640071/100000000000000 : ℝ)^3603 := by
    have hnat : (5289992311 : ℕ)^4627*100000000000000^3603 ≤ 44142696640071^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289992311 10000000000 44142696640071 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209478857/1250000000 : ℝ)^4627 ≤ (10086732438961/100000000000000 : ℝ)^3603 := by
    have hnat : (209478857 : ℕ)^4627*100000000000000^3603 ≤ 10086732438961^3603*1250000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209478857 1250000000 10086732438961 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720644973/5000000000 : ℝ)^4627 ≤ (45770570909219/100000000000000 : ℝ)^3603 := by
    have hnat : (2720644973 : ℕ)^4627*100000000000000^3603 ≤ 45770570909219^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720644973 5000000000 45770570909219 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289992311/10000000000 : ℝ), (-209478857/1250000000 : ℝ), (2720644973/5000000000 : ℝ)] ![(44142696640071/100000000000000 : ℝ), (10086732438961/100000000000000 : ℝ), (45770570909219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289992311/10000000000 : ℝ)|^4627 ≤ (44142696640071/100000000000000 : ℝ)^3603
        have hw : |(5289992311/10000000000 : ℝ)|=(5289992311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209478857/1250000000 : ℝ)|^4627 ≤ (10086732438961/100000000000000 : ℝ)^3603
        have hw : |(-209478857/1250000000 : ℝ)|=(209478857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720644973/5000000000 : ℝ)|^4627 ≤ (45770570909219/100000000000000 : ℝ)^3603
        have hw : |(2720644973/5000000000 : ℝ)|=(2720644973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s2_6 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289992551/10000000000 : ℝ)*x 0 + (2720645497/5000000000 : ℝ)*x 1 + (-837914529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289992551/10000000000 : ℝ)^4627 ≤ (11035674802987/25000000000000 : ℝ)^3603 := by
    have hnat : (5289992551 : ℕ)^4627*25000000000000^3603 ≤ 11035674802987^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289992551 10000000000 11035674802987 25000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720645497/5000000000 : ℝ)^4627 ≤ (1144264555753/2500000000000 : ℝ)^3603 := by
    have hnat : (2720645497 : ℕ)^4627*2500000000000^3603 ≤ 1144264555753^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720645497 5000000000 1144264555753 2500000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (837914529/5000000000 : ℝ)^4627 ≤ (10086718541189/100000000000000 : ℝ)^3603 := by
    have hnat : (837914529 : ℕ)^4627*100000000000000^3603 ≤ 10086718541189^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837914529 5000000000 10086718541189 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289992551/10000000000 : ℝ), (2720645497/5000000000 : ℝ), (-837914529/5000000000 : ℝ)] ![(11035674802987/25000000000000 : ℝ), (1144264555753/2500000000000 : ℝ), (10086718541189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289992551/10000000000 : ℝ)|^4627 ≤ (11035674802987/25000000000000 : ℝ)^3603
        have hw : |(5289992551/10000000000 : ℝ)|=(5289992551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720645497/5000000000 : ℝ)|^4627 ≤ (1144264555753/2500000000000 : ℝ)^3603
        have hw : |(2720645497/5000000000 : ℝ)|=(2720645497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-837914529/5000000000 : ℝ)|^4627 ≤ (10086718541189/100000000000000 : ℝ)^3603
        have hw : |(-837914529/5000000000 : ℝ)|=(837914529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_s2_7 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848834631/2000000000 : ℝ)*x 0 + (4527532287/10000000000 : ℝ)*x 1 + (1987794387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848834631/2000000000 : ℝ)^4627 ≤ (16633324688247/50000000000000 : ℝ)^3603 := by
    have hnat : (848834631 : ℕ)^4627*50000000000000^3603 ≤ 16633324688247^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848834631 2000000000 16633324688247 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4527532287/10000000000 : ℝ)^4627 ≤ (18072773157793/50000000000000 : ℝ)^3603 := by
    have hnat : (4527532287 : ℕ)^4627*50000000000000^3603 ≤ 18072773157793^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527532287 10000000000 18072773157793 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1987794387/5000000000 : ℝ)^4627 ≤ (30587804292907/100000000000000 : ℝ)^3603 := by
    have hnat : (1987794387 : ℕ)^4627*100000000000000^3603 ≤ 30587804292907^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987794387 5000000000 30587804292907 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848834631/2000000000 : ℝ), (4527532287/10000000000 : ℝ), (1987794387/5000000000 : ℝ)] ![(16633324688247/50000000000000 : ℝ), (18072773157793/50000000000000 : ℝ), (30587804292907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848834631/2000000000 : ℝ)|^4627 ≤ (16633324688247/50000000000000 : ℝ)^3603
        have hw : |(848834631/2000000000 : ℝ)|=(848834631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4527532287/10000000000 : ℝ)|^4627 ≤ (18072773157793/50000000000000 : ℝ)^3603
        have hw : |(4527532287/10000000000 : ℝ)|=(4527532287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1987794387/5000000000 : ℝ)|^4627 ≤ (30587804292907/100000000000000 : ℝ)^3603
        have hw : |(1987794387/5000000000 : ℝ)|=(1987794387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1565_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17801/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10791/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (633/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17801/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9013/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17801/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9013/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17801/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9013/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17801/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9013/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17801/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9013/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17801/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9013/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (9013/100000 : ℝ) ^ (4625/1024 : ℝ) ≤ (475884299869237/25000000000000000000 : ℝ) := by
    have hpowers : (9013/100000 : ℝ)^4625 ≤ (475884299869237/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9013 : ℕ)^4625*25000000000000000000^1024 ≤ 475884299869237^1024*100000^4625 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9013 100000 475884299869237 25000000000000000000 4625 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9013/100000 : ℝ)) (X := (475884299869237/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17801/100000 : ℝ) ^ (4625/1024 : ℝ) ≤ (8233528675365953/20000000000000000000 : ℝ) := by
    have hpowers : (17801/100000 : ℝ)^4625 ≤ (8233528675365953/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17801 : ℕ)^4625*20000000000000000000^1024 ≤ 8233528675365953^1024*100000^4625 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17801 100000 8233528675365953 20000000000000000000 4625 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17801/100000 : ℝ)) (X := (8233528675365953/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500475884299869237/12500000000000000000 : ℝ) ≤ (10000084289435841/10000000000000000 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (12500475884299869237/12500000000000000000 : ℝ)^1024 ≤ (10000084289435841/10000000000000000 : ℝ)^4625 := by
      have hnat : (12500475884299869237 : ℕ)^1024*10000000000000000^4625 ≤ 10000084289435841^4625*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500475884299869237 12500000000000000000 10000084289435841 10000000000000000 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084289435841/10000000000000000 : ℝ)) (X := (12500475884299869237/12500000000000000000 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043071180576306713/100000000000000000000 : ℝ) ≤ (200019069187249/200000000000000 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (100043071180576306713/100000000000000000000 : ℝ)^1024 ≤ (200019069187249/200000000000000 : ℝ)^4625 := by
      have hnat : (100043071180576306713 : ℕ)^1024*200000000000000^4625 ≤ 200019069187249^4625*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043071180576306713 100000000000000000000 200019069187249 200000000000000 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200019069187249/200000000000000 : ℝ)) (X := (100043071180576306713/100000000000000000000 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008233528675365953/10000000000000000000 : ℝ) ≤ (10001822629289059/10000000000000000 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (10008233528675365953/10000000000000000000 : ℝ)^1024 ≤ (10001822629289059/10000000000000000 : ℝ)^4625 := by
      have hnat : (10008233528675365953 : ℕ)^1024*10000000000000000^4625 ≤ 10001822629289059^4625*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008233528675365953 10000000000000000000 10001822629289059 10000000000000000 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001822629289059/10000000000000000 : ℝ)) (X := (10008233528675365953/10000000000000000000 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(475884299869237/25000000000000000000 : ℝ) ≤ ((43932536539232558437/43940000000000000000 : ℝ)+2*(869169926609/878800000000000 : ℝ)*(9013/100000 : ℝ))^(4625/1024 : ℝ) := by
    rw [show (43932536539232558437/43940000000000000000 : ℝ)+2*(869169926609/878800000000000 : ℝ)*(9013/100000 : ℝ)=(10000084289435841/10000000000000000 : ℝ) by norm_num, show 1+2*(475884299869237/25000000000000000000 : ℝ)=(12500475884299869237/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8233528675365953/20000000000000000000 : ℝ)+(475884299869237/25000000000000000000 : ℝ) ≤ ((43932536539232558437/43940000000000000000 : ℝ)+(869169926609/878800000000000 : ℝ)*((17801/100000 : ℝ)+(9013/100000 : ℝ)))^(4625/1024 : ℝ) := by
    rw [show (43932536539232558437/43940000000000000000 : ℝ)+(869169926609/878800000000000 : ℝ)*((17801/100000 : ℝ)+(9013/100000 : ℝ))=(200019069187249/200000000000000 : ℝ) by norm_num, show 1+(8233528675365953/20000000000000000000 : ℝ)+(475884299869237/25000000000000000000 : ℝ)=(100043071180576306713/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8233528675365953/20000000000000000000 : ℝ) ≤ ((43932536539232558437/43940000000000000000 : ℝ)+2*(869169926609/878800000000000 : ℝ)*(17801/100000 : ℝ))^(4625/1024 : ℝ) := by
    rw [show (43932536539232558437/43940000000000000000 : ℝ)+2*(869169926609/878800000000000 : ℝ)*(17801/100000 : ℝ)=(10001822629289059/10000000000000000 : ℝ) by norm_num, show 1+2*(8233528675365953/20000000000000000000 : ℝ)=(10008233528675365953/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43932536539232558437/43940000000000000000 : ℝ)*(X 1 0+X 2 0)+(869169926609/878800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (9013/100000 : ℝ)) (hi := (17801/100000 : ℝ)) (c := (43932536539232558437/43940000000000000000 : ℝ)) (alpha := (869169926609/878800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43932536539232558437/43940000000000000000 : ℝ)*(X 0 1+X 2 1)+(869169926609/878800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (9013/100000 : ℝ)) (hi := (17801/100000 : ℝ)) (c := (43932536539232558437/43940000000000000000 : ℝ)) (alpha := (869169926609/878800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43932536539232558437/43940000000000000000 : ℝ)*(X 0 2+X 1 2)+(869169926609/878800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (9013/100000 : ℝ)) (hi := (17801/100000 : ℝ)) (c := (43932536539232558437/43940000000000000000 : ℝ)) (alpha := (869169926609/878800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1789958281/10000000000 : ℝ)*X 0 0+(68034009/125000000 : ℝ)*X 0 1+(5205252031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352788699/10000000000 : ℝ)*X 1 0+(-1911867399/10000000000 : ℝ)*X 1 1+(5205252143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676394281/5000000000 : ℝ)*X 2 0+(5205252279/10000000000 : ℝ)*X 2 1+(-1911867401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4244077057/10000000000 : ℝ)*X 0 0+(1986110597/5000000000 : ℝ)*X 0 1+(4530871319/10000000000 : ℝ)*X 0 2+(4244077057/10000000000 : ℝ)*X 1 0+(1986110597/5000000000 : ℝ)*X 1 1+(4530871319/10000000000 : ℝ)*X 1 2+(4244077057/10000000000 : ℝ)*X 2 0+(1986110597/5000000000 : ℝ)*X 2 1+(4530871319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1789998723/10000000000 : ℝ)*X 0 0+(520667187/1000000000 : ℝ)*X 0 1+(5441289179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289992311/10000000000 : ℝ)*X 1 0+(-209478857/1250000000 : ℝ)*X 1 1+(2720644973/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289992551/10000000000 : ℝ)*X 2 0+(2720645497/5000000000 : ℝ)*X 2 1+(-837914529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((848834631/2000000000 : ℝ)*X 0 0+(4527532287/10000000000 : ℝ)*X 0 1+(1987794387/5000000000 : ℝ)*X 0 2+(848834631/2000000000 : ℝ)*X 1 0+(4527532287/10000000000 : ℝ)*X 1 1+(1987794387/5000000000 : ℝ)*X 1 2+(848834631/2000000000 : ℝ)*X 2 0+(4527532287/10000000000 : ℝ)*X 2 1+(1987794387/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22298517829981855309495464963/2197000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1621605661/100000000000000 : ℝ)*(base19) + (278367829/20000000000000 : ℝ)*(base23) + (16324163/25000000000000 : ℝ)*(lower2) + (11818821/5000000000000 : ℝ)*(upper3) + (24943819/20000000000000 : ℝ)*(upper5) + (3000591692442733/100000000000000 : ℝ)*(major0) + (3000591692442733/100000000000000 : ℝ)*(major1) + (3000591692442733/100000000000000 : ℝ)*(major2) + (4211108586610961/100000000000000 : ℝ)*(sp0) + (52639148616969/1250000000000 : ℝ)*(sp1) + (1052783029781009/25000000000000 : ℝ)*(sp2) + (895019335712129/50000000000000 : ℝ)*(sp3) + (1246217611/5000000000000 : ℝ)*(sp4) + (10864180349/100000000000000 : ℝ)*(sp7) + (1790049535604607/100000000000000 : ℝ)*(f.failure) + (4211133510963181/100000000000000 : ℝ)*(f.sum) + (158450158615603/43940000000000000000000000000 : ℝ)*base66 + (42617402962028338321/4394000000000000000000000000000000 : ℝ)*base67 + (6081811172812338321/4394000000000000000000000000000000 : ℝ)*base69 + (53500603335895661679/4394000000000000000000000000000000 : ℝ)*base72 + (205706324746497/43940000000000000000000000000 : ℝ)*base73 + (26655361501653661679/4394000000000000000000000000000000 : ℝ)*base76 + (9268005786183661679/4394000000000000000000000000000000 : ℝ)*base78 + (18954904935227661679/4394000000000000000000000000000000 : ℝ)*base80 + (99958288213917/43940000000000000000000000000 : ℝ)*base81 + (16510237/5000000000000000000000 : ℝ)*base89 + (16510237/5000000000000000000000 : ℝ)*base91 + (16510237/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19658586331499013743790214983/2197000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173789709/50000000000000 : ℝ)*(base15) + (3576409/2000000000000 : ℝ)*(lower2) + (65578337/100000000000000 : ℝ)*(upper3) + (5278611/10000000000000 : ℝ)*(lower4) + (3037021399488553/100000000000000 : ℝ)*(major0) + (3037021399488553/100000000000000 : ℝ)*(major1) + (3037021399488553/100000000000000 : ℝ)*(major2) + (3059212757/100000000000000 : ℝ)*(sp1) + (16454947869/50000000000000 : ℝ)*(sp2) + (688695693/100000000000000 : ℝ)*(sp3) + (532782532259339/12500000000000 : ℝ)*(sp4) + (2131128425641269/50000000000000 : ℝ)*(sp5) + (2131113674089487/50000000000000 : ℝ)*(sp6) + (452945388485651/25000000000000 : ℝ)*(sp7) + (1811782242638297/100000000000000 : ℝ)*(f.failure) + (532782532259339/12500000000000 : ℝ)*(f.sum) + (181981360472523/43940000000000000000000000000 : ℝ)*base66 + (7765645491203921661/4394000000000000000000000000000000 : ℝ)*base67 + (21372610902510078339/4394000000000000000000000000000000 : ℝ)*base70 + (24364975745484078339/4394000000000000000000000000000000 : ℝ)*base72 + (110951114243917/43940000000000000000000000000 : ℝ)*base73 + (33292696948404078339/4394000000000000000000000000000000 : ℝ)*base76 + (24676577028729921661/4394000000000000000000000000000000 : ℝ)*base77 + (1349688254288078339/4394000000000000000000000000000000 : ℝ)*base80 + (5845671342757/43940000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (16546027/5000000000000000000000 : ℝ)*base89 + (16546027/5000000000000000000000 : ℝ)*base91 + (16546027/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1565_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17801/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10791/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (633/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1565_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1565_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10791/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (633/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1565_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1565_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1565_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10791/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (633/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1565_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
