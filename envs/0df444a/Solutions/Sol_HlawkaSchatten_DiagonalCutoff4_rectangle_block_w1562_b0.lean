-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1562_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:24:41.303477+00:00
-- url     : https://prove2.me/submissions/46a485d2-4f0f-4597-955b-312e032ff638

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
theorem support_rectangle_w1562_s0_0 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-817031811/5000000000 : ℝ)*x 0 + (1468838821/2500000000 : ℝ)*x 1 + (4876128253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (817031811/5000000000 : ℝ)^4621 ≤ (4878328626297/50000000000000 : ℝ)^3597 := by
    have hnat : (817031811 : ℕ)^4621*50000000000000^3597 ≤ 4878328626297^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817031811 5000000000 4878328626297 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1468838821/2500000000 : ℝ)^4621 ≤ (10099790809417/20000000000000 : ℝ)^3597 := by
    have hnat : (1468838821 : ℕ)^4621*20000000000000^3597 ≤ 10099790809417^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468838821 2500000000 10099790809417 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4876128253/10000000000 : ℝ)^4621 ≤ (3974438868279/10000000000000 : ℝ)^3597 := by
    have hnat : (4876128253 : ℕ)^4621*10000000000000^3597 ≤ 3974438868279^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4876128253 10000000000 3974438868279 10000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-817031811/5000000000 : ℝ), (1468838821/2500000000 : ℝ), (4876128253/10000000000 : ℝ)] ![(4878328626297/50000000000000 : ℝ), (10099790809417/20000000000000 : ℝ), (3974438868279/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-817031811/5000000000 : ℝ)|^4621 ≤ (4878328626297/50000000000000 : ℝ)^3597
        have hw : |(-817031811/5000000000 : ℝ)|=(817031811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1468838821/2500000000 : ℝ)|^4621 ≤ (10099790809417/20000000000000 : ℝ)^3597
        have hw : |(1468838821/2500000000 : ℝ)|=(1468838821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4876128253/10000000000 : ℝ)|^4621 ≤ (3974438868279/10000000000000 : ℝ)^3597
        have hw : |(4876128253/10000000000 : ℝ)|=(4876128253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s0_1 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5467187599/10000000000 : ℝ)*x 0 + (-136915799/625000000 : ℝ)*x 1 + (4761844/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5467187599/10000000000 : ℝ)^4621 ≤ (1150933400123/2500000000000 : ℝ)^3597 := by
    have hnat : (5467187599 : ℕ)^4621*2500000000000^3597 ≤ 1150933400123^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467187599 10000000000 1150933400123 2500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136915799/625000000 : ℝ)^4621 ≤ (14218275272887/100000000000000 : ℝ)^3597 := by
    have hnat : (136915799 : ℕ)^4621*100000000000000^3597 ≤ 14218275272887^3597*625000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136915799 625000000 14218275272887 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4761844/9765625 : ℝ)^4621 ≤ (39744388714203/100000000000000 : ℝ)^3597 := by
    have hnat : (4761844 : ℕ)^4621*100000000000000^3597 ≤ 39744388714203^3597*9765625^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4761844 9765625 39744388714203 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5467187599/10000000000 : ℝ), (-136915799/625000000 : ℝ), (4761844/9765625 : ℝ)] ![(1150933400123/2500000000000 : ℝ), (14218275272887/100000000000000 : ℝ), (39744388714203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5467187599/10000000000 : ℝ)|^4621 ≤ (1150933400123/2500000000000 : ℝ)^3597
        have hw : |(5467187599/10000000000 : ℝ)|=(5467187599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136915799/625000000 : ℝ)|^4621 ≤ (14218275272887/100000000000000 : ℝ)^3597
        have hw : |(-136915799/625000000 : ℝ)|=(136915799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4761844/9765625 : ℝ)|^4621 ≤ (39744388714203/100000000000000 : ℝ)^3597
        have hw : |(4761844/9765625 : ℝ)|=(4761844/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s0_2 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2733593823/5000000000 : ℝ)*x 0 + (4876128201/10000000000 : ℝ)*x 1 + (-2190652791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2733593823/5000000000 : ℝ)^4621 ≤ (575466706417/1250000000000 : ℝ)^3597 := by
    have hnat : (2733593823 : ℕ)^4621*1250000000000^3597 ≤ 575466706417^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733593823 5000000000 575466706417 1250000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4876128201/10000000000 : ℝ)^4621 ≤ (39744388138287/100000000000000 : ℝ)^3597 := by
    have hnat : (4876128201 : ℕ)^4621*100000000000000^3597 ≤ 39744388138287^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4876128201 10000000000 39744388138287 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190652791/10000000000 : ℝ)^4621 ≤ (7109137665627/50000000000000 : ℝ)^3597 := by
    have hnat : (2190652791 : ℕ)^4621*50000000000000^3597 ≤ 7109137665627^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190652791 10000000000 7109137665627 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2733593823/5000000000 : ℝ), (4876128201/10000000000 : ℝ), (-2190652791/10000000000 : ℝ)] ![(575466706417/1250000000000 : ℝ), (39744388138287/100000000000000 : ℝ), (7109137665627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2733593823/5000000000 : ℝ)|^4621 ≤ (575466706417/1250000000000 : ℝ)^3597
        have hw : |(2733593823/5000000000 : ℝ)|=(2733593823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4876128201/10000000000 : ℝ)|^4621 ≤ (39744388138287/100000000000000 : ℝ)^3597
        have hw : |(4876128201/10000000000 : ℝ)|=(4876128201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190652791/10000000000 : ℝ)|^4621 ≤ (7109137665627/50000000000000 : ℝ)^3597
        have hw : |(-2190652791/10000000000 : ℝ)|=(2190652791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s0_3 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (826384179/2000000000 : ℝ)*x 0 + (3092738813/10000000000 : ℝ)*x 1 + (271931339/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826384179/2000000000 : ℝ)^4621 ≤ (32127542353507/100000000000000 : ℝ)^3597 := by
    have hnat : (826384179 : ℕ)^4621*100000000000000^3597 ≤ 32127542353507^3597*2000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826384179 2000000000 32127542353507 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3092738813/10000000000 : ℝ)^4621 ≤ (22143858811327/100000000000000 : ℝ)^3597 := by
    have hnat : (3092738813 : ℕ)^4621*100000000000000^3597 ≤ 22143858811327^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3092738813 10000000000 22143858811327 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271931339/500000000 : ℝ)^4621 ≤ (22864299412281/50000000000000 : ℝ)^3597 := by
    have hnat : (271931339 : ℕ)^4621*50000000000000^3597 ≤ 22864299412281^3597*500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271931339 500000000 22864299412281 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(826384179/2000000000 : ℝ), (3092738813/10000000000 : ℝ), (271931339/500000000 : ℝ)] ![(32127542353507/100000000000000 : ℝ), (22143858811327/100000000000000 : ℝ), (22864299412281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(826384179/2000000000 : ℝ)|^4621 ≤ (32127542353507/100000000000000 : ℝ)^3597
        have hw : |(826384179/2000000000 : ℝ)|=(826384179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3092738813/10000000000 : ℝ)|^4621 ≤ (22143858811327/100000000000000 : ℝ)^3597
        have hw : |(3092738813/10000000000 : ℝ)|=(3092738813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271931339/500000000 : ℝ)|^4621 ≤ (22864299412281/50000000000000 : ℝ)^3597
        have hw : |(271931339/500000000 : ℝ)|=(271931339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s0_4 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1637179027/10000000000 : ℝ)*x 0 + (1225338811/2500000000 : ℝ)*x 1 + (5849233223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1637179027/10000000000 : ℝ)^4621 ≤ (152821260403/1562500000000 : ℝ)^3597 := by
    have hnat : (1637179027 : ℕ)^4621*1562500000000^3597 ≤ 152821260403^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1637179027 10000000000 152821260403 1562500000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1225338811/2500000000 : ℝ)^4621 ≤ (40008739703851/100000000000000 : ℝ)^3597 := by
    have hnat : (1225338811 : ℕ)^4621*100000000000000^3597 ≤ 40008739703851^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225338811 2500000000 40008739703851 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5849233223/10000000000 : ℝ)^4621 ≤ (50210699613619/100000000000000 : ℝ)^3597 := by
    have hnat : (5849233223 : ℕ)^4621*100000000000000^3597 ≤ 50210699613619^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5849233223 10000000000 50210699613619 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1637179027/10000000000 : ℝ), (1225338811/2500000000 : ℝ), (5849233223/10000000000 : ℝ)] ![(152821260403/1562500000000 : ℝ), (40008739703851/100000000000000 : ℝ), (50210699613619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1637179027/10000000000 : ℝ)|^4621 ≤ (152821260403/1562500000000 : ℝ)^3597
        have hw : |(-1637179027/10000000000 : ℝ)|=(1637179027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1225338811/2500000000 : ℝ)|^4621 ≤ (40008739703851/100000000000000 : ℝ)^3597
        have hw : |(1225338811/2500000000 : ℝ)|=(1225338811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5849233223/10000000000 : ℝ)|^4621 ≤ (50210699613619/100000000000000 : ℝ)^3597
        have hw : |(5849233223/10000000000 : ℝ)|=(5849233223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s0_5 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194036417/10000000000 : ℝ)*x 0 + (-121754819/1000000000 : ℝ)*x 1 + (2924616677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194036417/10000000000 : ℝ)^4621 ≤ (5387961529961/12500000000000 : ℝ)^3597 := by
    have hnat : (5194036417 : ℕ)^4621*12500000000000^3597 ≤ 5387961529961^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194036417 10000000000 5387961529961 12500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121754819/1000000000 : ℝ)^4621 ≤ (133712133767/2000000000000 : ℝ)^3597 := by
    have hnat : (121754819 : ℕ)^4621*2000000000000^3597 ≤ 133712133767^3597*1000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121754819 1000000000 133712133767 2000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2924616677/5000000000 : ℝ)^4621 ≤ (25105350529137/50000000000000 : ℝ)^3597 := by
    have hnat : (2924616677 : ℕ)^4621*50000000000000^3597 ≤ 25105350529137^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2924616677 5000000000 25105350529137 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194036417/10000000000 : ℝ), (-121754819/1000000000 : ℝ), (2924616677/5000000000 : ℝ)] ![(5387961529961/12500000000000 : ℝ), (133712133767/2000000000000 : ℝ), (25105350529137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194036417/10000000000 : ℝ)|^4621 ≤ (5387961529961/12500000000000 : ℝ)^3597
        have hw : |(5194036417/10000000000 : ℝ)|=(5194036417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-121754819/1000000000 : ℝ)|^4621 ≤ (133712133767/2000000000000 : ℝ)^3597
        have hw : |(-121754819/1000000000 : ℝ)|=(121754819/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2924616677/5000000000 : ℝ)|^4621 ≤ (25105350529137/50000000000000 : ℝ)^3597
        have hw : |(2924616677/5000000000 : ℝ)|=(2924616677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s0_6 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194036407/10000000000 : ℝ)*x 0 + (5849233561/10000000000 : ℝ)*x 1 + (-1217547883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194036407/10000000000 : ℝ)^4621 ≤ (43103692133077/100000000000000 : ℝ)^3597 := by
    have hnat : (5194036407 : ℕ)^4621*100000000000000^3597 ≤ 43103692133077^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194036407 10000000000 43103692133077 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5849233561/10000000000 : ℝ)^4621 ≤ (50210703341049/100000000000000 : ℝ)^3597 := by
    have hnat : (5849233561 : ℕ)^4621*100000000000000^3597 ≤ 50210703341049^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5849233561 10000000000 50210703341049 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217547883/10000000000 : ℝ)^4621 ≤ (3342802261349/50000000000000 : ℝ)^3597 := by
    have hnat : (1217547883 : ℕ)^4621*50000000000000^3597 ≤ 3342802261349^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217547883 10000000000 3342802261349 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194036407/10000000000 : ℝ), (5849233561/10000000000 : ℝ), (-1217547883/10000000000 : ℝ)] ![(43103692133077/100000000000000 : ℝ), (50210703341049/100000000000000 : ℝ), (3342802261349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194036407/10000000000 : ℝ)|^4621 ≤ (43103692133077/100000000000000 : ℝ)^3597
        have hw : |(5194036407/10000000000 : ℝ)|=(5194036407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5849233561/10000000000 : ℝ)|^4621 ≤ (50210703341049/100000000000000 : ℝ)^3597
        have hw : |(5849233561/10000000000 : ℝ)|=(5849233561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1217547883/10000000000 : ℝ)|^4621 ≤ (3342802261349/50000000000000 : ℝ)^3597
        have hw : |(-1217547883/10000000000 : ℝ)|=(1217547883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s0_7 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165569353/400000000 : ℝ)*x 0 + (1344850239/2500000000 : ℝ)*x 1 + (394258159/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165569353/400000000 : ℝ)^4621 ≤ (6440121888407/20000000000000 : ℝ)^3597 := by
    have hnat : (165569353 : ℕ)^4621*20000000000000^3597 ≤ 6440121888407^3597*400000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165569353 400000000 6440121888407 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344850239/2500000000 : ℝ)^4621 ≤ (9017970088897/20000000000000 : ℝ)^3597 := by
    have hnat : (1344850239 : ℕ)^4621*20000000000000^3597 ≤ 9017970088897^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344850239 2500000000 9017970088897 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394258159/1250000000 : ℝ)^4621 ≤ (22709540106183/100000000000000 : ℝ)^3597 := by
    have hnat : (394258159 : ℕ)^4621*100000000000000^3597 ≤ 22709540106183^3597*1250000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394258159 1250000000 22709540106183 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165569353/400000000 : ℝ), (1344850239/2500000000 : ℝ), (394258159/1250000000 : ℝ)] ![(6440121888407/20000000000000 : ℝ), (9017970088897/20000000000000 : ℝ), (22709540106183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165569353/400000000 : ℝ)|^4621 ≤ (6440121888407/20000000000000 : ℝ)^3597
        have hw : |(165569353/400000000 : ℝ)|=(165569353/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344850239/2500000000 : ℝ)|^4621 ≤ (9017970088897/20000000000000 : ℝ)^3597
        have hw : |(1344850239/2500000000 : ℝ)|=(1344850239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(394258159/1250000000 : ℝ)|^4621 ≤ (22709540106183/100000000000000 : ℝ)^3597
        have hw : |(394258159/1250000000 : ℝ)|=(394258159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1562_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3449/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24853/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4619/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4619 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4619*1^1024 ≤ 0^1024*1^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4619/1024 : ℝ) ≤ (1603227725659388191/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4619 ≤ (1603227725659388191/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4619*100000000000000000000^1024 ≤ 1603227725659388191^1024*5^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1603227725659388191 100000000000000000000 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1603227725659388191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4619 := by
      have hnat : (1 : ℕ)^1024*1^4619 ≤ 1^4619*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101603227725659388191/100000000000000000000 : ℝ) ≤ (401412910876001/400000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (101603227725659388191/100000000000000000000 : ℝ)^1024 ≤ (401412910876001/400000000000000 : ℝ)^4619 := by
      have hnat : (101603227725659388191 : ℕ)^1024*400000000000000^4619 ≤ 401412910876001^4619*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101603227725659388191 100000000000000000000 401412910876001 400000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401412910876001/400000000000000 : ℝ)) (X := (101603227725659388191/100000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51603227725659388191/50000000000000000000 : ℝ) ≤ (201412910876001/200000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (51603227725659388191/50000000000000000000 : ℝ)^1024 ≤ (201412910876001/200000000000000 : ℝ)^4619 := by
      have hnat : (51603227725659388191 : ℕ)^1024*200000000000000^4619 ≤ 201412910876001^4619*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51603227725659388191 50000000000000000000 201412910876001 200000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (201412910876001/200000000000000 : ℝ)) (X := (51603227725659388191/50000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1412910876001/160000000000000 : ℝ)*(0 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1412910876001/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1603227725659388191/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1412910876001/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4619/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1412910876001/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(401412910876001/400000000000000 : ℝ) by norm_num, show 1+(1603227725659388191/100000000000000000000 : ℝ)+(0 : ℝ)=(101603227725659388191/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1603227725659388191/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1412910876001/160000000000000 : ℝ)*(2/5 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1412910876001/160000000000000 : ℝ)*(2/5 : ℝ)=(201412910876001/200000000000000 : ℝ) by norm_num, show 1+2*(1603227725659388191/100000000000000000000 : ℝ)=(51603227725659388191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1412910876001/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1412910876001/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1412910876001/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1412910876001/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1412910876001/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1412910876001/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-817031811/5000000000 : ℝ)*X 0 0+(1468838821/2500000000 : ℝ)*X 0 1+(4876128253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5467187599/10000000000 : ℝ)*X 1 0+(-136915799/625000000 : ℝ)*X 1 1+(4761844/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2733593823/5000000000 : ℝ)*X 2 0+(4876128201/10000000000 : ℝ)*X 2 1+(-2190652791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((826384179/2000000000 : ℝ)*X 0 0+(3092738813/10000000000 : ℝ)*X 0 1+(271931339/500000000 : ℝ)*X 0 2+(826384179/2000000000 : ℝ)*X 1 0+(3092738813/10000000000 : ℝ)*X 1 1+(271931339/500000000 : ℝ)*X 1 2+(826384179/2000000000 : ℝ)*X 2 0+(3092738813/10000000000 : ℝ)*X 2 1+(271931339/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1637179027/10000000000 : ℝ)*X 0 0+(1225338811/2500000000 : ℝ)*X 0 1+(5849233223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5194036417/10000000000 : ℝ)*X 1 0+(-121754819/1000000000 : ℝ)*X 1 1+(2924616677/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5194036407/10000000000 : ℝ)*X 2 0+(5849233561/10000000000 : ℝ)*X 2 1+(-1217547883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((165569353/400000000 : ℝ)*X 0 0+(1344850239/2500000000 : ℝ)*X 0 1+(394258159/1250000000 : ℝ)*X 0 2+(165569353/400000000 : ℝ)*X 1 0+(1344850239/2500000000 : ℝ)*X 1 1+(394258159/1250000000 : ℝ)*X 1 2+(165569353/400000000 : ℝ)*X 2 0+(1344850239/2500000000 : ℝ)*X 2 1+(394258159/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21057695658583887526443/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50096831/100000000000000 : ℝ)*(base1) + (548427467/50000000000000 : ℝ)*(base19) + (69091149/6250000000000 : ℝ)*(base23) + (142147813/100000000000000 : ℝ)*(upper3) + (71147387/50000000000000 : ℝ)*(upper5) + (713531421119827/100000000000000 : ℝ)*(major0) + (713531421119827/100000000000000 : ℝ)*(major1) + (713531421119827/100000000000000 : ℝ)*(major2) + (100077741228343/10000000000000 : ℝ)*(sp0) + (250195083024271/25000000000000 : ℝ)*(sp1) + (500390161746817/50000000000000 : ℝ)*(sp2) + (213139727655919/50000000000000 : ℝ)*(sp3) + (203338271/5000000000000 : ℝ)*(sp4) + (346479633/20000000000000 : ℝ)*(sp7) + (213140618903417/50000000000000 : ℝ)*(f.failure) + (500390714476009/50000000000000 : ℝ)*(f.sum) + (9519091108173/8000000000000000000000000000 : ℝ)*base66 + (111050970572173/16000000000000000000000000000 : ℝ)*base68 + (82467343948173/16000000000000000000000000000 : ℝ)*base70 + (57486599644173/16000000000000000000000000000 : ℝ)*base72 + (16814897852173/8000000000000000000000000000 : ℝ)*base74 + (49656288812173/16000000000000000000000000000 : ℝ)*base76 + (58375947612173/16000000000000000000000000000 : ℝ)*base78 + (66256823916173/16000000000000000000000000000 : ℝ)*base80 + (8465160636173/8000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (18801439/2500000000000000000000 : ℝ)*base89 + (18801439/2500000000000000000000 : ℝ)*base91 + (18801439/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18801776313637701318753/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100565203/5000000000000 : ℝ)*(base19) + (253816409/12500000000000 : ℝ)*(base23) + (1734413/50000000000000 : ℝ)*(base32) + (78280479/25000000000000 : ℝ)*(upper3) + (289581493/100000000000000 : ℝ)*(upper5) + (188044844628251/25000000000000 : ℝ)*(major0) + (188044844628251/25000000000000 : ℝ)*(major1) + (188044844628251/25000000000000 : ℝ)*(major2) + (5503452899/100000000000000 : ℝ)*(sp1) + (5907684587/100000000000000 : ℝ)*(sp2) + (105498796461383/10000000000000 : ℝ)*(sp4) + (105498044985687/10000000000000 : ℝ)*(sp5) + (1054980026397971/100000000000000 : ℝ)*(sp6) + (449370475580409/100000000000000 : ℝ)*(sp7) + (89874095809847/20000000000000 : ℝ)*(f.failure) + (105498796461383/10000000000000 : ℝ)*(f.sum) + (4439620474251/2000000000000000000000000000 : ℝ)*base65 + (5679979591749/4000000000000000000000000000 : ℝ)*base68 + (37427318847749/4000000000000000000000000000 : ℝ)*base70 + (7054927640251/4000000000000000000000000000 : ℝ)*base71 + (5670232728251/2000000000000000000000000000 : ℝ)*base73 + (5858446983749/4000000000000000000000000000 : ℝ)*base76 + (19524704791749/4000000000000000000000000000 : ℝ)*base78 + (18055252383749/4000000000000000000000000000 : ℝ)*base80 + (4949754571749/2000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (692751/1000000000000000000000 : ℝ)*base90 + (692751/1000000000000000000000 : ℝ)*base92 + (692751/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1562_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24853/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1562_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1562_s1_0 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-887347753/5000000000 : ℝ)*x 0 + (43276807/78125000 : ℝ)*x 1 + (2560723041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (887347753/5000000000 : ℝ)^4621 ≤ (339010529881/3125000000000 : ℝ)^3597 := by
    have hnat : (887347753 : ℕ)^4621*3125000000000^3597 ≤ 339010529881^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887347753 5000000000 339010529881 3125000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43276807/78125000 : ℝ)^4621 ≤ (46820324253483/100000000000000 : ℝ)^3597 := by
    have hnat : (43276807 : ℕ)^4621*100000000000000^3597 ≤ 46820324253483^3597*78125000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43276807 78125000 46820324253483 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2560723041/5000000000 : ℝ)^4621 ≤ (21165669383523/50000000000000 : ℝ)^3597 := by
    have hnat : (2560723041 : ℕ)^4621*50000000000000^3597 ≤ 21165669383523^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560723041 5000000000 21165669383523 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-887347753/5000000000 : ℝ), (43276807/78125000 : ℝ), (2560723041/5000000000 : ℝ)] ![(339010529881/3125000000000 : ℝ), (46820324253483/100000000000000 : ℝ), (21165669383523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-887347753/5000000000 : ℝ)|^4621 ≤ (339010529881/3125000000000 : ℝ)^3597
        have hw : |(-887347753/5000000000 : ℝ)|=(887347753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43276807/78125000 : ℝ)|^4621 ≤ (46820324253483/100000000000000 : ℝ)^3597
        have hw : |(43276807/78125000 : ℝ)|=(43276807/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2560723041/5000000000 : ℝ)|^4621 ≤ (21165669383523/50000000000000 : ℝ)^3597
        have hw : |(2560723041/5000000000 : ℝ)|=(2560723041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s1_1 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377799097/10000000000 : ℝ)*x 0 + (-62297421/312500000 : ℝ)*x 1 + (5121446037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377799097/10000000000 : ℝ)^4621 ≤ (22536301072471/50000000000000 : ℝ)^3597 := by
    have hnat : (5377799097 : ℕ)^4621*50000000000000^3597 ≤ 22536301072471^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377799097 10000000000 22536301072471 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62297421/312500000 : ℝ)^4621 ≤ (6298029773721/50000000000000 : ℝ)^3597 := by
    have hnat : (62297421 : ℕ)^4621*50000000000000^3597 ≤ 6298029773721^3597*312500000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62297421 312500000 6298029773721 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5121446037/10000000000 : ℝ)^4621 ≤ (10582834572303/25000000000000 : ℝ)^3597 := by
    have hnat : (5121446037 : ℕ)^4621*25000000000000^3597 ≤ 10582834572303^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121446037 10000000000 10582834572303 25000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377799097/10000000000 : ℝ), (-62297421/312500000 : ℝ), (5121446037/10000000000 : ℝ)] ![(22536301072471/50000000000000 : ℝ), (6298029773721/50000000000000 : ℝ), (10582834572303/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377799097/10000000000 : ℝ)|^4621 ≤ (22536301072471/50000000000000 : ℝ)^3597
        have hw : |(5377799097/10000000000 : ℝ)|=(5377799097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-62297421/312500000 : ℝ)|^4621 ≤ (6298029773721/50000000000000 : ℝ)^3597
        have hw : |(-62297421/312500000 : ℝ)|=(62297421/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5121446037/10000000000 : ℝ)|^4621 ≤ (10582834572303/25000000000000 : ℝ)^3597
        have hw : |(5121446037/10000000000 : ℝ)|=(5121446037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s1_2 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688899509/5000000000 : ℝ)*x 0 + (80022601/156250000 : ℝ)*x 1 + (-996758509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688899509/5000000000 : ℝ)^4621 ≤ (11268150323583/25000000000000 : ℝ)^3597 := by
    have hnat : (2688899509 : ℕ)^4621*25000000000000^3597 ≤ 11268150323583^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688899509 5000000000 11268150323583 25000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80022601/156250000 : ℝ)^4621 ≤ (42331342823329/100000000000000 : ℝ)^3597 := by
    have hnat : (80022601 : ℕ)^4621*100000000000000^3597 ≤ 42331342823329^3597*156250000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80022601 156250000 42331342823329 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (996758509/5000000000 : ℝ)^4621 ≤ (62980279311/500000000000 : ℝ)^3597 := by
    have hnat : (996758509 : ℕ)^4621*500000000000^3597 ≤ 62980279311^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996758509 5000000000 62980279311 500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688899509/5000000000 : ℝ), (80022601/156250000 : ℝ), (-996758509/5000000000 : ℝ)] ![(11268150323583/25000000000000 : ℝ), (42331342823329/100000000000000 : ℝ), (62980279311/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688899509/5000000000 : ℝ)|^4621 ≤ (11268150323583/25000000000000 : ℝ)^3597
        have hw : |(2688899509/5000000000 : ℝ)|=(2688899509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80022601/156250000 : ℝ)|^4621 ≤ (42331342823329/100000000000000 : ℝ)^3597
        have hw : |(80022601/156250000 : ℝ)|=(80022601/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-996758509/5000000000 : ℝ)|^4621 ≤ (62980279311/500000000000 : ℝ)^3597
        have hw : |(-996758509/5000000000 : ℝ)|=(996758509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s1_3 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2115685873/5000000000 : ℝ)*x 0 + (3763794967/10000000000 : ℝ)*x 1 + (37960807/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115685873/5000000000 : ℝ)^4621 ≤ (66248677517/200000000000 : ℝ)^3597 := by
    have hnat : (2115685873 : ℕ)^4621*200000000000^3597 ≤ 66248677517^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115685873 5000000000 66248677517 200000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3763794967/10000000000 : ℝ)^4621 ≤ (14249001966379/50000000000000 : ℝ)^3597 := by
    have hnat : (3763794967 : ℕ)^4621*50000000000000^3597 ≤ 14249001966379^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3763794967 10000000000 14249001966379 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37960807/80000000 : ℝ)^4621 ≤ (38377657291317/100000000000000 : ℝ)^3597 := by
    have hnat : (37960807 : ℕ)^4621*100000000000000^3597 ≤ 38377657291317^3597*80000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37960807 80000000 38377657291317 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2115685873/5000000000 : ℝ), (3763794967/10000000000 : ℝ), (37960807/80000000 : ℝ)] ![(66248677517/200000000000 : ℝ), (14249001966379/50000000000000 : ℝ), (38377657291317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2115685873/5000000000 : ℝ)|^4621 ≤ (66248677517/200000000000 : ℝ)^3597
        have hw : |(2115685873/5000000000 : ℝ)|=(2115685873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3763794967/10000000000 : ℝ)|^4621 ≤ (14249001966379/50000000000000 : ℝ)^3597
        have hw : |(3763794967/10000000000 : ℝ)|=(3763794967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(37960807/80000000 : ℝ)|^4621 ≤ (38377657291317/100000000000000 : ℝ)^3597
        have hw : |(37960807/80000000 : ℝ)|=(37960807/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s1_4 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-44372931/250000000 : ℝ)*x 0 + (5125806043/10000000000 : ℝ)*x 1 + (885601/1600000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44372931/250000000 : ℝ)^4621 ≤ (10850078261253/100000000000000 : ℝ)^3597 := by
    have hnat : (44372931 : ℕ)^4621*100000000000000^3597 ≤ 10850078261253^3597*250000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44372931 250000000 10850078261253 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5125806043/10000000000 : ℝ)^4621 ≤ (8475528161851/20000000000000 : ℝ)^3597 := by
    have hnat : (5125806043 : ℕ)^4621*20000000000000^3597 ≤ 8475528161851^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125806043 10000000000 8475528161851 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (885601/1600000 : ℝ)^4621 ≤ (2923267557293/6250000000000 : ℝ)^3597 := by
    have hnat : (885601 : ℕ)^4621*6250000000000^3597 ≤ 2923267557293^3597*1600000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885601 1600000 2923267557293 6250000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44372931/250000000 : ℝ), (5125806043/10000000000 : ℝ), (885601/1600000 : ℝ)] ![(10850078261253/100000000000000 : ℝ), (8475528161851/20000000000000 : ℝ), (2923267557293/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44372931/250000000 : ℝ)|^4621 ≤ (10850078261253/100000000000000 : ℝ)^3597
        have hw : |(-44372931/250000000 : ℝ)|=(44372931/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5125806043/10000000000 : ℝ)|^4621 ≤ (8475528161851/20000000000000 : ℝ)^3597
        have hw : |(5125806043/10000000000 : ℝ)|=(5125806043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(885601/1600000 : ℝ)|^4621 ≤ (2923267557293/6250000000000 : ℝ)^3597
        have hw : |(885601/1600000 : ℝ)|=(885601/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s1_5 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267092903/10000000000 : ℝ)*x 0 + (-315991417/2000000000 : ℝ)*x 1 + (1107001319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267092903/10000000000 : ℝ)^4621 ≤ (5485514285107/12500000000000 : ℝ)^3597 := by
    have hnat : (5267092903 : ℕ)^4621*12500000000000^3597 ≤ 5485514285107^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267092903 10000000000 5485514285107 12500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (315991417/2000000000 : ℝ)^4621 ≤ (2335900260911/25000000000000 : ℝ)^3597 := by
    have hnat : (315991417 : ℕ)^4621*25000000000000^3597 ≤ 2335900260911^3597*2000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315991417 2000000000 2335900260911 25000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107001319/2000000000 : ℝ)^4621 ≤ (23386142330987/50000000000000 : ℝ)^3597 := by
    have hnat : (1107001319 : ℕ)^4621*50000000000000^3597 ≤ 23386142330987^3597*2000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107001319 2000000000 23386142330987 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267092903/10000000000 : ℝ), (-315991417/2000000000 : ℝ), (1107001319/2000000000 : ℝ)] ![(5485514285107/12500000000000 : ℝ), (2335900260911/25000000000000 : ℝ), (23386142330987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267092903/10000000000 : ℝ)|^4621 ≤ (5485514285107/12500000000000 : ℝ)^3597
        have hw : |(5267092903/10000000000 : ℝ)|=(5267092903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-315991417/2000000000 : ℝ)|^4621 ≤ (2335900260911/25000000000000 : ℝ)^3597
        have hw : |(-315991417/2000000000 : ℝ)|=(315991417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1107001319/2000000000 : ℝ)|^4621 ≤ (23386142330987/50000000000000 : ℝ)^3597
        have hw : |(1107001319/2000000000 : ℝ)|=(1107001319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s1_6 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267092537/10000000000 : ℝ)*x 0 + (5535006723/10000000000 : ℝ)*x 1 + (-1579957417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267092537/10000000000 : ℝ)^4621 ≤ (1097102759083/2500000000000 : ℝ)^3597 := by
    have hnat : (5267092537 : ℕ)^4621*2500000000000^3597 ≤ 1097102759083^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267092537 10000000000 1097102759083 2500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5535006723/10000000000 : ℝ)^4621 ≤ (4677228605153/10000000000000 : ℝ)^3597 := by
    have hnat : (5535006723 : ℕ)^4621*10000000000000^3597 ≤ 4677228605153^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5535006723 10000000000 4677228605153 10000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1579957417/10000000000 : ℝ)^4621 ≤ (4671801782989/50000000000000 : ℝ)^3597 := by
    have hnat : (1579957417 : ℕ)^4621*50000000000000^3597 ≤ 4671801782989^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579957417 10000000000 4671801782989 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267092537/10000000000 : ℝ), (5535006723/10000000000 : ℝ), (-1579957417/10000000000 : ℝ)] ![(1097102759083/2500000000000 : ℝ), (4677228605153/10000000000000 : ℝ), (4671801782989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267092537/10000000000 : ℝ)|^4621 ≤ (1097102759083/2500000000000 : ℝ)^3597
        have hw : |(5267092537/10000000000 : ℝ)|=(5267092537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5535006723/10000000000 : ℝ)|^4621 ≤ (4677228605153/10000000000000 : ℝ)^3597
        have hw : |(5535006723/10000000000 : ℝ)|=(5535006723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1579957417/10000000000 : ℝ)|^4621 ≤ (4671801782989/50000000000000 : ℝ)^3597
        have hw : |(-1579957417/10000000000 : ℝ)|=(1579957417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s1_7 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4231891233/10000000000 : ℝ)*x 0 + (4734865377/10000000000 : ℝ)*x 1 + (188709189/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4231891233/10000000000 : ℝ)^4621 ≤ (258824712873/781250000000 : ℝ)^3597 := by
    have hnat : (4231891233 : ℕ)^4621*781250000000^3597 ≤ 258824712873^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231891233 10000000000 258824712873 781250000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4734865377/10000000000 : ℝ)^4621 ≤ (2391958747221/6250000000000 : ℝ)^3597 := by
    have hnat : (4734865377 : ℕ)^4621*6250000000000^3597 ≤ 2391958747221^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4734865377 10000000000 2391958747221 6250000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188709189/500000000 : ℝ)^4621 ≤ (446860887187/1562500000000 : ℝ)^3597 := by
    have hnat : (188709189 : ℕ)^4621*1562500000000^3597 ≤ 446860887187^3597*500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188709189 500000000 446860887187 1562500000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4231891233/10000000000 : ℝ), (4734865377/10000000000 : ℝ), (188709189/500000000 : ℝ)] ![(258824712873/781250000000 : ℝ), (2391958747221/6250000000000 : ℝ), (446860887187/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4231891233/10000000000 : ℝ)|^4621 ≤ (258824712873/781250000000 : ℝ)^3597
        have hw : |(4231891233/10000000000 : ℝ)|=(4231891233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4734865377/10000000000 : ℝ)|^4621 ≤ (2391958747221/6250000000000 : ℝ)^3597
        have hw : |(4734865377/10000000000 : ℝ)|=(4734865377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188709189/500000000 : ℝ)|^4621 ≤ (446860887187/1562500000000 : ℝ)^3597
        have hw : |(188709189/500000000 : ℝ)|=(188709189/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1562_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4489/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17829/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3449/100000 : ℝ) ^ (4619/1024 : ℝ) ≤ (12673045820469/50000000000000000000 : ℝ) := by
    have hpowers : (3449/100000 : ℝ)^4619 ≤ (12673045820469/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3449 : ℕ)^4619*50000000000000000000^1024 ≤ 12673045820469^1024*100000^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3449 100000 12673045820469 50000000000000000000 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3449/100000 : ℝ)) (X := (12673045820469/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24853/100000 : ℝ) ^ (4619/1024 : ℝ) ≤ (37474835123749367/20000000000000000000 : ℝ) := by
    have hpowers : (24853/100000 : ℝ)^4619 ≤ (37474835123749367/20000000000000000000 : ℝ)^1024 := by
      have hnat : (24853 : ℕ)^4619*20000000000000000000^1024 ≤ 37474835123749367^1024*100000^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24853 100000 37474835123749367 20000000000000000000 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24853/100000 : ℝ)) (X := (37474835123749367/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000012673045820469/25000000000000000000 : ℝ) ≤ (5000000561905017/5000000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (25000012673045820469/25000000000000000000 : ℝ)^1024 ≤ (5000000561905017/5000000000000000 : ℝ)^4619 := by
      have hnat : (25000012673045820469 : ℕ)^1024*5000000000000000^4619 ≤ 5000000561905017^4619*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000012673045820469 25000000000000000000 5000000561905017 5000000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000561905017/5000000000000000 : ℝ)) (X := (25000012673045820469/25000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100187399521710387773/100000000000000000000 : ℝ) ≤ (2501037872485049/2500000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (100187399521710387773/100000000000000000000 : ℝ)^1024 ≤ (2501037872485049/2500000000000000 : ℝ)^4619 := by
      have hnat : (100187399521710387773 : ℕ)^1024*2500000000000000^4619 ≤ 2501037872485049^4619*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100187399521710387773 100000000000000000000 2501037872485049 2500000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501037872485049/2500000000000000 : ℝ)) (X := (100187399521710387773/100000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10037474835123749367/10000000000000000000 : ℝ) ≤ (5004150928035179/5000000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (10037474835123749367/10000000000000000000 : ℝ)^1024 ≤ (5004150928035179/5000000000000000 : ℝ)^4619 := by
      have hnat : (10037474835123749367 : ℕ)^1024*5000000000000000^4619 ≤ 5004150928035179^4619*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10037474835123749367 10000000000000000000 5004150928035179 5000000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004150928035179/5000000000000000 : ℝ)) (X := (10037474835123749367/10000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12673045820469/50000000000000000000 : ℝ) ≤ ((10700569741423205513/10702000000000000000 : ℝ)+2*(2075183065081/1070200000000000 : ℝ)*(3449/100000 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (10700569741423205513/10702000000000000000 : ℝ)+2*(2075183065081/1070200000000000 : ℝ)*(3449/100000 : ℝ)=(5000000561905017/5000000000000000 : ℝ) by norm_num, show 1+2*(12673045820469/50000000000000000000 : ℝ)=(25000012673045820469/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37474835123749367/20000000000000000000 : ℝ)+(12673045820469/50000000000000000000 : ℝ) ≤ ((10700569741423205513/10702000000000000000 : ℝ)+(2075183065081/1070200000000000 : ℝ)*((24853/100000 : ℝ)+(3449/100000 : ℝ)))^(4619/1024 : ℝ) := by
    rw [show (10700569741423205513/10702000000000000000 : ℝ)+(2075183065081/1070200000000000 : ℝ)*((24853/100000 : ℝ)+(3449/100000 : ℝ))=(2501037872485049/2500000000000000 : ℝ) by norm_num, show 1+(37474835123749367/20000000000000000000 : ℝ)+(12673045820469/50000000000000000000 : ℝ)=(100187399521710387773/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37474835123749367/20000000000000000000 : ℝ) ≤ ((10700569741423205513/10702000000000000000 : ℝ)+2*(2075183065081/1070200000000000 : ℝ)*(24853/100000 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (10700569741423205513/10702000000000000000 : ℝ)+2*(2075183065081/1070200000000000 : ℝ)*(24853/100000 : ℝ)=(5004150928035179/5000000000000000 : ℝ) by norm_num, show 1+2*(37474835123749367/20000000000000000000 : ℝ)=(10037474835123749367/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10700569741423205513/10702000000000000000 : ℝ)*(X 1 0+X 2 0)+(2075183065081/1070200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (3449/100000 : ℝ)) (hi := (24853/100000 : ℝ)) (c := (10700569741423205513/10702000000000000000 : ℝ)) (alpha := (2075183065081/1070200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10700569741423205513/10702000000000000000 : ℝ)*(X 0 1+X 2 1)+(2075183065081/1070200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (3449/100000 : ℝ)) (hi := (24853/100000 : ℝ)) (c := (10700569741423205513/10702000000000000000 : ℝ)) (alpha := (2075183065081/1070200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10700569741423205513/10702000000000000000 : ℝ)*(X 0 2+X 1 2)+(2075183065081/1070200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (3449/100000 : ℝ)) (hi := (24853/100000 : ℝ)) (c := (10700569741423205513/10702000000000000000 : ℝ)) (alpha := (2075183065081/1070200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-887347753/5000000000 : ℝ)*X 0 0+(43276807/78125000 : ℝ)*X 0 1+(2560723041/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377799097/10000000000 : ℝ)*X 1 0+(-62297421/312500000 : ℝ)*X 1 1+(5121446037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2688899509/5000000000 : ℝ)*X 2 0+(80022601/156250000 : ℝ)*X 2 1+(-996758509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2115685873/5000000000 : ℝ)*X 0 0+(3763794967/10000000000 : ℝ)*X 0 1+(37960807/80000000 : ℝ)*X 0 2+(2115685873/5000000000 : ℝ)*X 1 0+(3763794967/10000000000 : ℝ)*X 1 1+(37960807/80000000 : ℝ)*X 1 2+(2115685873/5000000000 : ℝ)*X 2 0+(3763794967/10000000000 : ℝ)*X 2 1+(37960807/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-44372931/250000000 : ℝ)*X 0 0+(5125806043/10000000000 : ℝ)*X 0 1+(885601/1600000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5267092903/10000000000 : ℝ)*X 1 0+(-315991417/2000000000 : ℝ)*X 1 1+(1107001319/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5267092537/10000000000 : ℝ)*X 2 0+(5535006723/10000000000 : ℝ)*X 2 1+(-1579957417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4231891233/10000000000 : ℝ)*X 0 0+(4734865377/10000000000 : ℝ)*X 0 1+(188709189/500000000 : ℝ)*X 0 2+(4231891233/10000000000 : ℝ)*X 1 0+(4734865377/10000000000 : ℝ)*X 1 1+(188709189/500000000 : ℝ)*X 1 2+(4231891233/10000000000 : ℝ)*X 2 0+(4734865377/10000000000 : ℝ)*X 2 1+(188709189/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2129250762656816886658255323/267550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138321889/100000000000000 : ℝ)*(base1) + (1752245549/100000000000000 : ℝ)*(base19) + (343420061/20000000000000 : ℝ)*(base23) + (16404489/20000000000000 : ℝ)*(upper3) + (165183411/50000000000000 : ℝ)*(upper5) + (852880513367819/50000000000000 : ℝ)*(major0) + (852880513367819/50000000000000 : ℝ)*(major1) + (852880513367819/50000000000000 : ℝ)*(major2) + (1196220790165637/50000000000000 : ℝ)*(sp0) + (1196228201744889/50000000000000 : ℝ)*(sp1) + (1196228219317511/50000000000000 : ℝ)*(sp2) + (509528770712303/50000000000000 : ℝ)*(sp3) + (8356862971/50000000000000 : ℝ)*(sp4) + (5952711833/100000000000000 : ℝ)*(sp7) + (1019063632458327/100000000000000 : ℝ)*(f.failure) + (1196229077867663/50000000000000 : ℝ)*(f.sum) + (835925117363/836093750000000000000000000 : ℝ)*base66 + (1707926307139323853/535100000000000000000000000000000 : ℝ)*base68 + (6894609032544823853/535100000000000000000000000000000 : ℝ)*base70 + (3958551544367123853/535100000000000000000000000000000 : ℝ)*base72 + (24473953045977/13377500000000000000000000000 : ℝ)*base73 + (4359093235556623853/535100000000000000000000000000000 : ℝ)*base76 + (5454090724710123853/535100000000000000000000000000000 : ℝ)*base78 + (4177864216429123853/535100000000000000000000000000000 : ℝ)*base80 + (99963247334131/26755000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7155409/5000000000000000000000 : ℝ)*base89 + (7155409/5000000000000000000000 : ℝ)*base91 + (7155409/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85658036416239019548148719/13377500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14183061/1250000000000 : ℝ)*(base19) + (255612571/25000000000000 : ℝ)*(base23) + (18773909/50000000000000 : ℝ)*(upper2) + (209299191/100000000000000 : ℝ)*(upper3) + (111868187/100000000000000 : ℝ)*(upper5) + (87117926037621/5000000000000 : ℝ)*(major0) + (87117926037621/5000000000000 : ℝ)*(major1) + (87117926037621/5000000000000 : ℝ)*(major2) + (4613952073/50000000000000 : ℝ)*(sp1) + (1715518341/20000000000000 : ℝ)*(sp2) + (488757790333719/20000000000000 : ℝ)*(sp4) + (2443778589119569/100000000000000 : ℝ)*(sp5) + (1221889675813303/50000000000000 : ℝ)*(sp6) + (1040927876398163/100000000000000 : ℝ)*(sp7) + (1040927876398163/100000000000000 : ℝ)*(f.failure) + (488757790333719/20000000000000 : ℝ)*(f.sum) + (7428750510227/5351000000000000000000000000 : ℝ)*base66 + (115991463570745427/53510000000000000000000000000000 : ℝ)*base68 + (252297104188285427/53510000000000000000000000000000 : ℝ)*base70 + (49624238558134573/53510000000000000000000000000000 : ℝ)*base71 + (229915079783/334437500000000000000000000 : ℝ)*base73 + (78518467344855427/53510000000000000000000000000000 : ℝ)*base76 + (205485229193795427/53510000000000000000000000000000 : ℝ)*base78 + (288258008412975427/53510000000000000000000000000000 : ℝ)*base80 + (2360830625473/2675500000000000000000000000 : ℝ)*base82 + (24445579/5000000000000000000000 : ℝ)*base90 + (24445579/5000000000000000000000 : ℝ)*base92 + (24445579/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1562_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4489/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17829/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1562_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1562_s2_0 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-897013579/5000000000 : ℝ)*x 0 + (2721748831/5000000000 : ℝ)*x 1 + (5204792403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897013579/5000000000 : ℝ)^4621 ≤ (2200076586687/20000000000000 : ℝ)^3597 := by
    have hnat : (897013579 : ℕ)^4621*20000000000000^3597 ≤ 2200076586687^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897013579 5000000000 2200076586687 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721748831/5000000000 : ℝ)^4621 ≤ (45781219585749/100000000000000 : ℝ)^3597 := by
    have hnat : (2721748831 : ℕ)^4621*100000000000000^3597 ≤ 45781219585749^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721748831 5000000000 45781219585749 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5204792403/10000000000 : ℝ)^4621 ≤ (43218397457617/100000000000000 : ℝ)^3597 := by
    have hnat : (5204792403 : ℕ)^4621*100000000000000^3597 ≤ 43218397457617^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204792403 10000000000 43218397457617 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-897013579/5000000000 : ℝ), (2721748831/5000000000 : ℝ), (5204792403/10000000000 : ℝ)] ![(2200076586687/20000000000000 : ℝ), (45781219585749/100000000000000 : ℝ), (43218397457617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-897013579/5000000000 : ℝ)|^4621 ≤ (2200076586687/20000000000000 : ℝ)^3597
        have hw : |(-897013579/5000000000 : ℝ)|=(897013579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721748831/5000000000 : ℝ)|^4621 ≤ (45781219585749/100000000000000 : ℝ)^3597
        have hw : |(2721748831/5000000000 : ℝ)|=(2721748831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5204792403/10000000000 : ℝ)|^4621 ≤ (43218397457617/100000000000000 : ℝ)^3597
        have hw : |(5204792403/10000000000 : ℝ)|=(5204792403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s2_1 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669134057/1250000000 : ℝ)*x 0 + (-1916588411/10000000000 : ℝ)*x 1 + (2602395999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669134057/1250000000 : ℝ)^4621 ≤ (5600817424529/12500000000000 : ℝ)^3597 := by
    have hnat : (669134057 : ℕ)^4621*12500000000000^3597 ≤ 5600817424529^3597*1250000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669134057 1250000000 5600817424529 12500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1916588411/10000000000 : ℝ)^4621 ≤ (5987533724703/50000000000000 : ℝ)^3597 := by
    have hnat : (1916588411 : ℕ)^4621*50000000000000^3597 ≤ 5987533724703^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916588411 10000000000 5987533724703 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2602395999/5000000000 : ℝ)^4621 ≤ (43218393137299/100000000000000 : ℝ)^3597 := by
    have hnat : (2602395999 : ℕ)^4621*100000000000000^3597 ≤ 43218393137299^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602395999 5000000000 43218393137299 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669134057/1250000000 : ℝ), (-1916588411/10000000000 : ℝ), (2602395999/5000000000 : ℝ)] ![(5600817424529/12500000000000 : ℝ), (5987533724703/50000000000000 : ℝ), (43218393137299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669134057/1250000000 : ℝ)|^4621 ≤ (5600817424529/12500000000000 : ℝ)^3597
        have hw : |(669134057/1250000000 : ℝ)|=(669134057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1916588411/10000000000 : ℝ)|^4621 ≤ (5987533724703/50000000000000 : ℝ)^3597
        have hw : |(-1916588411/10000000000 : ℝ)|=(1916588411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2602395999/5000000000 : ℝ)|^4621 ≤ (43218393137299/100000000000000 : ℝ)^3597
        have hw : |(2602395999/5000000000 : ℝ)|=(2602395999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s2_2 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353072259/10000000000 : ℝ)*x 0 + (1301198017/2500000000 : ℝ)*x 1 + (-1916588581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353072259/10000000000 : ℝ)^4621 ≤ (44806537277871/100000000000000 : ℝ)^3597 := by
    have hnat : (5353072259 : ℕ)^4621*100000000000000^3597 ≤ 44806537277871^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353072259 10000000000 44806537277871 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1301198017/2500000000 : ℝ)^4621 ≤ (2160919694201/5000000000000 : ℝ)^3597 := by
    have hnat : (1301198017 : ℕ)^4621*5000000000000^3597 ≤ 2160919694201^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301198017 2500000000 2160919694201 5000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1916588581/10000000000 : ℝ)^4621 ≤ (11975068813969/100000000000000 : ℝ)^3597 := by
    have hnat : (1916588581 : ℕ)^4621*100000000000000^3597 ≤ 11975068813969^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916588581 10000000000 11975068813969 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353072259/10000000000 : ℝ), (1301198017/2500000000 : ℝ), (-1916588581/10000000000 : ℝ)] ![(44806537277871/100000000000000 : ℝ), (2160919694201/5000000000000 : ℝ), (11975068813969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353072259/10000000000 : ℝ)|^4621 ≤ (44806537277871/100000000000000 : ℝ)^3597
        have hw : |(5353072259/10000000000 : ℝ)|=(5353072259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1301198017/2500000000 : ℝ)|^4621 ≤ (2160919694201/5000000000000 : ℝ)^3597
        have hw : |(1301198017/2500000000 : ℝ)|=(1301198017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1916588581/10000000000 : ℝ)|^4621 ≤ (11975068813969/100000000000000 : ℝ)^3597
        have hw : |(-1916588581/10000000000 : ℝ)|=(1916588581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s2_3 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061341061/2500000000 : ℝ)*x 0 + (397269029/1000000000 : ℝ)*x 1 + (4533101387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061341061/2500000000 : ℝ)^4621 ≤ (3326512526519/10000000000000 : ℝ)^3597 := by
    have hnat : (1061341061 : ℕ)^4621*10000000000000^3597 ≤ 3326512526519^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061341061 2500000000 3326512526519 10000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397269029/1000000000 : ℝ)^4621 ≤ (7636449414957/25000000000000 : ℝ)^3597 := by
    have hnat : (397269029 : ℕ)^4621*25000000000000^3597 ≤ 7636449414957^3597*1000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397269029 1000000000 7636449414957 25000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4533101387/10000000000 : ℝ)^4621 ≤ (141363582271/390625000000 : ℝ)^3597 := by
    have hnat : (4533101387 : ℕ)^4621*390625000000^3597 ≤ 141363582271^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533101387 10000000000 141363582271 390625000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061341061/2500000000 : ℝ), (397269029/1000000000 : ℝ), (4533101387/10000000000 : ℝ)] ![(3326512526519/10000000000000 : ℝ), (7636449414957/25000000000000 : ℝ), (141363582271/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061341061/2500000000 : ℝ)|^4621 ≤ (3326512526519/10000000000000 : ℝ)^3597
        have hw : |(1061341061/2500000000 : ℝ)|=(1061341061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(397269029/1000000000 : ℝ)|^4621 ≤ (7636449414957/25000000000000 : ℝ)^3597
        have hw : |(397269029/1000000000 : ℝ)|=(397269029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4533101387/10000000000 : ℝ)|^4621 ≤ (141363582271/390625000000 : ℝ)^3597
        have hw : |(4533101387/10000000000 : ℝ)|=(4533101387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s2_4 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1794068137/10000000000 : ℝ)*x 0 + (1041244439/2000000000 : ℝ)*x 1 + (5442056021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1794068137/10000000000 : ℝ)^4621 ≤ (2750176434021/25000000000000 : ℝ)^3597 := by
    have hnat : (1794068137 : ℕ)^4621*25000000000000^3597 ≤ 2750176434021^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794068137 10000000000 2750176434021 25000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041244439/2000000000 : ℝ)^4621 ≤ (5404206286791/12500000000000 : ℝ)^3597 := by
    have hnat : (1041244439 : ℕ)^4621*12500000000000^3597 ≤ 5404206286791^3597*2000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041244439 2000000000 5404206286791 12500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442056021/10000000000 : ℝ)^4621 ≤ (2288282197827/5000000000000 : ℝ)^3597 := by
    have hnat : (5442056021 : ℕ)^4621*5000000000000^3597 ≤ 2288282197827^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442056021 10000000000 2288282197827 5000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1794068137/10000000000 : ℝ), (1041244439/2000000000 : ℝ), (5442056021/10000000000 : ℝ)] ![(2750176434021/25000000000000 : ℝ), (5404206286791/12500000000000 : ℝ), (2288282197827/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1794068137/10000000000 : ℝ)|^4621 ≤ (2750176434021/25000000000000 : ℝ)^3597
        have hw : |(-1794068137/10000000000 : ℝ)|=(1794068137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041244439/2000000000 : ℝ)|^4621 ≤ (5404206286791/12500000000000 : ℝ)^3597
        have hw : |(1041244439/2000000000 : ℝ)|=(1041244439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442056021/10000000000 : ℝ)|^4621 ≤ (2288282197827/5000000000000 : ℝ)^3597
        have hw : |(5442056021/10000000000 : ℝ)|=(5442056021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s2_5 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289971719/10000000000 : ℝ)*x 0 + (-335864991/2000000000 : ℝ)*x 1 + (5442056607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289971719/10000000000 : ℝ)^4621 ≤ (22064576184237/50000000000000 : ℝ)^3597 := by
    have hnat : (5289971719 : ℕ)^4621*50000000000000^3597 ≤ 22064576184237^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289971719 10000000000 22064576184237 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335864991/2000000000 : ℝ)^4621 ≤ (5052598667169/50000000000000 : ℝ)^3597 := by
    have hnat : (335864991 : ℕ)^4621*50000000000000^3597 ≤ 5052598667169^3597*2000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335864991 2000000000 5052598667169 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442056607/10000000000 : ℝ)^4621 ≤ (45765650287503/100000000000000 : ℝ)^3597 := by
    have hnat : (5442056607 : ℕ)^4621*100000000000000^3597 ≤ 45765650287503^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442056607 10000000000 45765650287503 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289971719/10000000000 : ℝ), (-335864991/2000000000 : ℝ), (5442056607/10000000000 : ℝ)] ![(22064576184237/50000000000000 : ℝ), (5052598667169/50000000000000 : ℝ), (45765650287503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289971719/10000000000 : ℝ)|^4621 ≤ (22064576184237/50000000000000 : ℝ)^3597
        have hw : |(5289971719/10000000000 : ℝ)|=(5289971719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-335864991/2000000000 : ℝ)|^4621 ≤ (5052598667169/50000000000000 : ℝ)^3597
        have hw : |(-335864991/2000000000 : ℝ)|=(335864991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442056607/10000000000 : ℝ)|^4621 ≤ (45765650287503/100000000000000 : ℝ)^3597
        have hw : |(5442056607/10000000000 : ℝ)|=(5442056607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s2_6 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644985931/5000000000 : ℝ)*x 0 + (2721028877/5000000000 : ℝ)*x 1 + (-1679323153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644985931/5000000000 : ℝ)^4621 ≤ (8825830780197/20000000000000 : ℝ)^3597 := by
    have hnat : (2644985931 : ℕ)^4621*20000000000000^3597 ≤ 8825830780197^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644985931 5000000000 8825830780197 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721028877/5000000000 : ℝ)^4621 ≤ (9153132535867/20000000000000 : ℝ)^3597 := by
    have hnat : (2721028877 : ℕ)^4621*20000000000000^3597 ≤ 9153132535867^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721028877 5000000000 9153132535867 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1679323153/10000000000 : ℝ)^4621 ≤ (10105183404043/100000000000000 : ℝ)^3597 := by
    have hnat : (1679323153 : ℕ)^4621*100000000000000^3597 ≤ 10105183404043^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679323153 10000000000 10105183404043 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644985931/5000000000 : ℝ), (2721028877/5000000000 : ℝ), (-1679323153/10000000000 : ℝ)] ![(8825830780197/20000000000000 : ℝ), (9153132535867/20000000000000 : ℝ), (10105183404043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644985931/5000000000 : ℝ)|^4621 ≤ (8825830780197/20000000000000 : ℝ)^3597
        have hw : |(2644985931/5000000000 : ℝ)|=(2644985931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721028877/5000000000 : ℝ)|^4621 ≤ (9153132535867/20000000000000 : ℝ)^3597
        have hw : |(2721028877/5000000000 : ℝ)|=(2721028877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1679323153/10000000000 : ℝ)|^4621 ≤ (10105183404043/100000000000000 : ℝ)^3597
        have hw : |(-1679323153/10000000000 : ℝ)|=(1679323153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s2_7 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4245461119/10000000000 : ℝ)*x 0 + (1132436123/2500000000 : ℝ)*x 1 + (124252381/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4245461119/10000000000 : ℝ)^4621 ≤ (33266100440871/100000000000000 : ℝ)^3597 := by
    have hnat : (4245461119 : ℕ)^4621*100000000000000^3597 ≤ 33266100440871^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245461119 10000000000 33266100440871 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132436123/2500000000 : ℝ)^4621 ≤ (1807732620407/5000000000000 : ℝ)^3597 := by
    have hnat : (1132436123 : ℕ)^4621*5000000000000^3597 ≤ 1807732620407^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132436123 2500000000 1807732620407 5000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124252381/312500000 : ℝ)^4621 ≤ (30579247138193/100000000000000 : ℝ)^3597 := by
    have hnat : (124252381 : ℕ)^4621*100000000000000^3597 ≤ 30579247138193^3597*312500000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124252381 312500000 30579247138193 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4245461119/10000000000 : ℝ), (1132436123/2500000000 : ℝ), (124252381/312500000 : ℝ)] ![(33266100440871/100000000000000 : ℝ), (1807732620407/5000000000000 : ℝ), (30579247138193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4245461119/10000000000 : ℝ)|^4621 ≤ (33266100440871/100000000000000 : ℝ)^3597
        have hw : |(4245461119/10000000000 : ℝ)|=(4245461119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132436123/2500000000 : ℝ)|^4621 ≤ (1807732620407/5000000000000 : ℝ)^3597
        have hw : |(1132436123/2500000000 : ℝ)|=(1132436123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(124252381/312500000 : ℝ)|^4621 ≤ (30579247138193/100000000000000 : ℝ)^3597
        have hw : |(124252381/312500000 : ℝ)|=(124252381/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1562_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17829/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5387/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15833/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17829/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17829/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17829/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17829/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17829/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17829/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (4489/50000 : ℝ) ^ (4619/1024 : ℝ) ≤ (189698136139301/10000000000000000000 : ℝ) := by
    have hpowers : (4489/50000 : ℝ)^4619 ≤ (189698136139301/10000000000000000000 : ℝ)^1024 := by
      have hnat : (4489 : ℕ)^4619*10000000000000000000^1024 ≤ 189698136139301^1024*50000^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4489 50000 189698136139301 10000000000000000000 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4489/50000 : ℝ)) (X := (189698136139301/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17829/100000 : ℝ) ^ (4619/1024 : ℝ) ≤ (8376390078603251/20000000000000000000 : ℝ) := by
    have hpowers : (17829/100000 : ℝ)^4619 ≤ (8376390078603251/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17829 : ℕ)^4619*20000000000000000000^1024 ≤ 8376390078603251^1024*100000^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17829 100000 8376390078603251 20000000000000000000 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17829/100000 : ℝ)) (X := (8376390078603251/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000189698136139301/5000000000000000000 : ℝ) ≤ (2500021027064677/2500000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (5000189698136139301/5000000000000000000 : ℝ)^1024 ≤ (2500021027064677/2500000000000000 : ℝ)^4619 := by
      have hnat : (5000189698136139301 : ℕ)^1024*2500000000000000^4619 ≤ 2500021027064677^4619*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000189698136139301 5000000000000000000 2500021027064677 2500000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500021027064677/2500000000000000 : ℝ)) (X := (5000189698136139301/5000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008755786350881853/20000000000000000000 : ℝ) ≤ (5000485191498139/5000000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (20008755786350881853/20000000000000000000 : ℝ)^1024 ≤ (5000485191498139/5000000000000000 : ℝ)^4619 := by
      have hnat : (20008755786350881853 : ℕ)^1024*5000000000000000^4619 ≤ 5000485191498139^4619*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008755786350881853 20000000000000000000 5000485191498139 5000000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000485191498139/5000000000000000 : ℝ)) (X := (20008755786350881853/20000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008376390078603251/10000000000000000000 : ℝ) ≤ (1250232082216731/1250000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (10008376390078603251/10000000000000000000 : ℝ)^1024 ≤ (1250232082216731/1250000000000000 : ℝ)^4619 := by
      have hnat : (10008376390078603251 : ℕ)^1024*1250000000000000^4619 ≤ 1250232082216731^4619*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008376390078603251 10000000000000000000 1250232082216731 1250000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250232082216731/1250000000000000 : ℝ)) (X := (10008376390078603251/10000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(189698136139301/10000000000000000000 : ℝ) ≤ ((22123707623252504397/22127500000000000000 : ℝ)+2*(88627473757/88510000000000 : ℝ)*(4489/50000 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (22123707623252504397/22127500000000000000 : ℝ)+2*(88627473757/88510000000000 : ℝ)*(4489/50000 : ℝ)=(2500021027064677/2500000000000000 : ℝ) by norm_num, show 1+2*(189698136139301/10000000000000000000 : ℝ)=(5000189698136139301/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8376390078603251/20000000000000000000 : ℝ)+(189698136139301/10000000000000000000 : ℝ) ≤ ((22123707623252504397/22127500000000000000 : ℝ)+(88627473757/88510000000000 : ℝ)*((17829/100000 : ℝ)+(4489/50000 : ℝ)))^(4619/1024 : ℝ) := by
    rw [show (22123707623252504397/22127500000000000000 : ℝ)+(88627473757/88510000000000 : ℝ)*((17829/100000 : ℝ)+(4489/50000 : ℝ))=(5000485191498139/5000000000000000 : ℝ) by norm_num, show 1+(8376390078603251/20000000000000000000 : ℝ)+(189698136139301/10000000000000000000 : ℝ)=(20008755786350881853/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8376390078603251/20000000000000000000 : ℝ) ≤ ((22123707623252504397/22127500000000000000 : ℝ)+2*(88627473757/88510000000000 : ℝ)*(17829/100000 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (22123707623252504397/22127500000000000000 : ℝ)+2*(88627473757/88510000000000 : ℝ)*(17829/100000 : ℝ)=(1250232082216731/1250000000000000 : ℝ) by norm_num, show 1+2*(8376390078603251/20000000000000000000 : ℝ)=(10008376390078603251/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22123707623252504397/22127500000000000000 : ℝ)*(X 1 0+X 2 0)+(88627473757/88510000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (4489/50000 : ℝ)) (hi := (17829/100000 : ℝ)) (c := (22123707623252504397/22127500000000000000 : ℝ)) (alpha := (88627473757/88510000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22123707623252504397/22127500000000000000 : ℝ)*(X 0 1+X 2 1)+(88627473757/88510000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (4489/50000 : ℝ)) (hi := (17829/100000 : ℝ)) (c := (22123707623252504397/22127500000000000000 : ℝ)) (alpha := (88627473757/88510000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22123707623252504397/22127500000000000000 : ℝ)*(X 0 2+X 1 2)+(88627473757/88510000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (4489/50000 : ℝ)) (hi := (17829/100000 : ℝ)) (c := (22123707623252504397/22127500000000000000 : ℝ)) (alpha := (88627473757/88510000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-897013579/5000000000 : ℝ)*X 0 0+(2721748831/5000000000 : ℝ)*X 0 1+(5204792403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669134057/1250000000 : ℝ)*X 1 0+(-1916588411/10000000000 : ℝ)*X 1 1+(2602395999/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353072259/10000000000 : ℝ)*X 2 0+(1301198017/2500000000 : ℝ)*X 2 1+(-1916588581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061341061/2500000000 : ℝ)*X 0 0+(397269029/1000000000 : ℝ)*X 0 1+(4533101387/10000000000 : ℝ)*X 0 2+(1061341061/2500000000 : ℝ)*X 1 0+(397269029/1000000000 : ℝ)*X 1 1+(4533101387/10000000000 : ℝ)*X 1 2+(1061341061/2500000000 : ℝ)*X 2 0+(397269029/1000000000 : ℝ)*X 2 1+(4533101387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1794068137/10000000000 : ℝ)*X 0 0+(1041244439/2000000000 : ℝ)*X 0 1+(5442056021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289971719/10000000000 : ℝ)*X 1 0+(-335864991/2000000000 : ℝ)*X 1 1+(5442056607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644985931/5000000000 : ℝ)*X 2 0+(2721028877/5000000000 : ℝ)*X 2 1+(-1679323153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4245461119/10000000000 : ℝ)*X 0 0+(1132436123/2500000000 : ℝ)*X 0 1+(124252381/312500000 : ℝ)*X 0 2+(4245461119/10000000000 : ℝ)*X 1 0+(1132436123/2500000000 : ℝ)*X 1 1+(124252381/312500000 : ℝ)*X 1 2+(4245461119/10000000000 : ℝ)*X 2 0+(1132436123/2500000000 : ℝ)*X 2 1+(124252381/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1460691014239638323805078477/276593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (185368979/25000000000000 : ℝ)*(base19) + (118297083/20000000000000 : ℝ)*(base23) + (10405739/20000000000000 : ℝ)*(lower2) + (185887599/100000000000000 : ℝ)*(upper3) + (6783293/12500000000000 : ℝ)*(lower4) + (12147247/100000000000000 : ℝ)*(upper5) + (746710739962703/25000000000000 : ℝ)*(major0) + (746710739962703/25000000000000 : ℝ)*(major1) + (746710739962703/25000000000000 : ℝ)*(major2) + (6545737851083/156250000000 : ℝ)*(sp0) + (1047317870804301/25000000000000 : ℝ)*(sp1) + (2094635816603853/50000000000000 : ℝ)*(sp2) + (1784408245178919/100000000000000 : ℝ)*(sp3) + (1318449079/25000000000000 : ℝ)*(sp7) + (356882703795047/20000000000000 : ℝ)*(f.failure) + (6545737851083/156250000000 : ℝ)*(f.sum) + (9402520745439/1106375000000000000000000000 : ℝ)*base66 + (47633363071389247/10437500000000000000000000000000 : ℝ)*base67 + (52017496513826747/10437500000000000000000000000000 : ℝ)*base69 + (10579513270514247/10437500000000000000000000000000 : ℝ)*base71 + (1984127114493/885100000000000000000000000 : ℝ)*base73 + (3036748967326747/10437500000000000000000000000000 : ℝ)*base75 + (22568889017610753/10437500000000000000000000000000 : ℝ)*base78 + (121431075982110753/10437500000000000000000000000000 : ℝ)*base80 + (38517788512921/8851000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5315649/1000000000000000000000 : ℝ)*base89 + (5315649/1000000000000000000000 : ℝ)*base91 + (5315649/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2670435858159491955441315519/1106375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143479649/100000000000000 : ℝ)*(base8) + (19046017/5000000000000 : ℝ)*(base15) + (21955549/10000000000000 : ℝ)*(base29) + (16035981/20000000000000 : ℝ)*(lower2) + (3204157/25000000000000 : ℝ)*(lower4) + (3023205788384701/100000000000000 : ℝ)*(major0) + (3023206007940191/100000000000000 : ℝ)*(major1) + (3023206007940191/100000000000000 : ℝ)*(major2) + (14749662803/50000000000000 : ℝ)*(sp2) + (53287831/5000000000000 : ℝ)*(sp3) + (33922192742389/800000000000 : ℝ)*(sp4) + (1060068408950611/25000000000000 : ℝ)*(sp5) + (4240244517397177/100000000000000 : ℝ)*(sp6) + (361227326677893/20000000000000 : ℝ)*(sp7) + (361227539829217/20000000000000 : ℝ)*(f.failure) + (2120137118139137/50000000000000 : ℝ)*(f.sum) + (16028272344671/2212750000000000000000000000 : ℝ)*base65 + (4615880684226041/41750000000000000000000000000000 : ℝ)*base68 + (124164420408273959/41750000000000000000000000000000 : ℝ)*base69 + (9485390413873469703/2212750000000000000000000000000000 : ℝ)*base72 + (541821200829/2212750000000000000000000000 : ℝ)*base74 + (4108792671172769827/2212750000000000000000000000000000 : ℝ)*base75 + (8517286261003530297/2212750000000000000000000000000000 : ℝ)*base77 + (3671656124218269827/2212750000000000000000000000000000 : ℝ)*base79 + (1457213035141/8851000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2330039/1000000000000000000000 : ℝ)*base89 + (2330039/1000000000000000000000 : ℝ)*base91 + (2330039/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1562_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17829/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15833/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1562_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1562_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15833/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1562_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1562_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1562_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15833/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1562_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
