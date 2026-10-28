-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1180_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:49:18.430316+00:00
-- url     : https://prove2.me/submissions/17c57dd6-675b-45de-8f7f-44a0f36649c4

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
theorem support_rectangle_w1180_s3_0 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-429087683/2000000000 : ℝ)*x 0 + (5425376493/10000000000 : ℝ)*x 1 + (5235531179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429087683/2000000000 : ℝ)^8373 ≤ (13033607836711/100000000000000 : ℝ)^6325 := by
    have hnat : (429087683 : ℕ)^8373*100000000000000^6325 ≤ 13033607836711^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429087683 2000000000 13033607836711 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425376493/10000000000 : ℝ)^8373 ≤ (44508170852049/100000000000000 : ℝ)^6325 := by
    have hnat : (5425376493 : ℕ)^8373*100000000000000^6325 ≤ 44508170852049^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425376493 10000000000 44508170852049 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235531179/10000000000 : ℝ)^8373 ≤ (21229110651831/50000000000000 : ℝ)^6325 := by
    have hnat : (5235531179 : ℕ)^8373*50000000000000^6325 ≤ 21229110651831^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235531179 10000000000 21229110651831 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429087683/2000000000 : ℝ), (5425376493/10000000000 : ℝ), (5235531179/10000000000 : ℝ)] ![(13033607836711/100000000000000 : ℝ), (44508170852049/100000000000000 : ℝ), (21229110651831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429087683/2000000000 : ℝ)|^8373 ≤ (13033607836711/100000000000000 : ℝ)^6325
        have hw : |(-429087683/2000000000 : ℝ)|=(429087683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425376493/10000000000 : ℝ)|^8373 ≤ (44508170852049/100000000000000 : ℝ)^6325
        have hw : |(5425376493/10000000000 : ℝ)|=(5425376493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235531179/10000000000 : ℝ)|^8373 ≤ (21229110651831/50000000000000 : ℝ)^6325
        have hw : |(5235531179/10000000000 : ℝ)|=(5235531179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s3_1 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070579009/2000000000 : ℝ)*x 0 + (-1121201311/5000000000 : ℝ)*x 1 + (5235530983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070579009/2000000000 : ℝ)^8373 ≤ (1093068222963/2500000000000 : ℝ)^6325 := by
    have hnat : (1070579009 : ℕ)^8373*2500000000000^6325 ≤ 1093068222963^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070579009 2000000000 1093068222963 2500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121201311/5000000000 : ℝ)^8373 ≤ (13819051862471/100000000000000 : ℝ)^6325 := by
    have hnat : (1121201311 : ℕ)^8373*100000000000000^6325 ≤ 13819051862471^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121201311 5000000000 13819051862471 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235530983/10000000000 : ℝ)^8373 ≤ (42458219199507/100000000000000 : ℝ)^6325 := by
    have hnat : (5235530983 : ℕ)^8373*100000000000000^6325 ≤ 42458219199507^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235530983 10000000000 42458219199507 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070579009/2000000000 : ℝ), (-1121201311/5000000000 : ℝ), (5235530983/10000000000 : ℝ)] ![(1093068222963/2500000000000 : ℝ), (13819051862471/100000000000000 : ℝ), (42458219199507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070579009/2000000000 : ℝ)|^8373 ≤ (1093068222963/2500000000000 : ℝ)^6325
        have hw : |(1070579009/2000000000 : ℝ)|=(1070579009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1121201311/5000000000 : ℝ)|^8373 ≤ (13819051862471/100000000000000 : ℝ)^6325
        have hw : |(-1121201311/5000000000 : ℝ)|=(1121201311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235530983/10000000000 : ℝ)|^8373 ≤ (42458219199507/100000000000000 : ℝ)^6325
        have hw : |(5235530983/10000000000 : ℝ)|=(5235530983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s3_2 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352895133/10000000000 : ℝ)*x 0 + (654441369/1250000000 : ℝ)*x 1 + (-2242402547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352895133/10000000000 : ℝ)^8373 ≤ (1366335308439/3125000000000 : ℝ)^6325 := by
    have hnat : (5352895133 : ℕ)^8373*3125000000000^6325 ≤ 1366335308439^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352895133 10000000000 1366335308439 3125000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654441369/1250000000 : ℝ)^8373 ≤ (42458218866707/100000000000000 : ℝ)^6325 := by
    have hnat : (654441369 : ℕ)^8373*100000000000000^6325 ≤ 42458218866707^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654441369 1250000000 42458218866707 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242402547/10000000000 : ℝ)^8373 ≤ (13819051250619/100000000000000 : ℝ)^6325 := by
    have hnat : (2242402547 : ℕ)^8373*100000000000000^6325 ≤ 13819051250619^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242402547 10000000000 13819051250619 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352895133/10000000000 : ℝ), (654441369/1250000000 : ℝ), (-2242402547/10000000000 : ℝ)] ![(1366335308439/3125000000000 : ℝ), (42458218866707/100000000000000 : ℝ), (13819051250619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352895133/10000000000 : ℝ)|^8373 ≤ (1366335308439/3125000000000 : ℝ)^6325
        have hw : |(5352895133/10000000000 : ℝ)|=(5352895133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654441369/1250000000 : ℝ)|^8373 ≤ (42458218866707/100000000000000 : ℝ)^6325
        have hw : |(654441369/1250000000 : ℝ)|=(654441369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2242402547/10000000000 : ℝ)|^8373 ≤ (13819051250619/100000000000000 : ℝ)^6325
        have hw : |(-2242402547/10000000000 : ℝ)|=(2242402547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s3_3 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871464151/2000000000 : ℝ)*x 0 + (83423149/200000000 : ℝ)*x 1 + (1137916767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871464151/2000000000 : ℝ)^8373 ≤ (16648335359693/50000000000000 : ℝ)^6325 := by
    have hnat : (871464151 : ℕ)^8373*50000000000000^6325 ≤ 16648335359693^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871464151 2000000000 16648335359693 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83423149/200000000 : ℝ)^8373 ≤ (31426626693069/100000000000000 : ℝ)^6325 := by
    have hnat : (83423149 : ℕ)^8373*100000000000000^6325 ≤ 31426626693069^6325*200000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83423149 200000000 31426626693069 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137916767/2500000000 : ℝ)^8373 ≤ (17638351293527/50000000000000 : ℝ)^6325 := by
    have hnat : (1137916767 : ℕ)^8373*50000000000000^6325 ≤ 17638351293527^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137916767 2500000000 17638351293527 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871464151/2000000000 : ℝ), (83423149/200000000 : ℝ), (1137916767/2500000000 : ℝ)] ![(16648335359693/50000000000000 : ℝ), (31426626693069/100000000000000 : ℝ), (17638351293527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871464151/2000000000 : ℝ)|^8373 ≤ (16648335359693/50000000000000 : ℝ)^6325
        have hw : |(871464151/2000000000 : ℝ)|=(871464151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(83423149/200000000 : ℝ)|^8373 ≤ (31426626693069/100000000000000 : ℝ)^6325
        have hw : |(83423149/200000000 : ℝ)|=(83423149/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1137916767/2500000000 : ℝ)|^8373 ≤ (17638351293527/50000000000000 : ℝ)^6325
        have hw : |(1137916767/2500000000 : ℝ)|=(1137916767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s3_4 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072727373/5000000000 : ℝ)*x 0 + (5236249049/10000000000 : ℝ)*x 1 + (5424654729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072727373/5000000000 : ℝ)^8373 ≤ (6516869586157/50000000000000 : ℝ)^6325 := by
    have hnat : (1072727373 : ℕ)^8373*50000000000000^6325 ≤ 6516869586157^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072727373 5000000000 6516869586157 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236249049/10000000000 : ℝ)^8373 ≤ (1358909701/3200000000 : ℝ)^6325 := by
    have hnat : (5236249049 : ℕ)^8373*3200000000^6325 ≤ 1358909701^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236249049 10000000000 1358909701 3200000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424654729/10000000000 : ℝ)^8373 ≤ (8900066530597/20000000000000 : ℝ)^6325 := by
    have hnat : (5424654729 : ℕ)^8373*20000000000000^6325 ≤ 8900066530597^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424654729 10000000000 8900066530597 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072727373/5000000000 : ℝ), (5236249049/10000000000 : ℝ), (5424654729/10000000000 : ℝ)] ![(6516869586157/50000000000000 : ℝ), (1358909701/3200000000 : ℝ), (8900066530597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072727373/5000000000 : ℝ)|^8373 ≤ (6516869586157/50000000000000 : ℝ)^6325
        have hw : |(-1072727373/5000000000 : ℝ)|=(1072727373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236249049/10000000000 : ℝ)|^8373 ≤ (1358909701/3200000000 : ℝ)^6325
        have hw : |(5236249049/10000000000 : ℝ)|=(5236249049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424654729/10000000000 : ℝ)|^8373 ≤ (8900066530597/20000000000000 : ℝ)^6325
        have hw : |(5424654729/10000000000 : ℝ)|=(5424654729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s3_5 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304667233/10000000000 : ℝ)*x 0 + (-1026639321/5000000000 : ℝ)*x 1 + (169520459/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304667233/10000000000 : ℝ)^8373 ≤ (10800503081223/25000000000000 : ℝ)^6325 := by
    have hnat : (5304667233 : ℕ)^8373*25000000000000^6325 ≤ 10800503081223^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304667233 10000000000 10800503081223 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026639321/5000000000 : ℝ)^8373 ≤ (12297655449637/100000000000000 : ℝ)^6325 := by
    have hnat : (1026639321 : ℕ)^8373*100000000000000^6325 ≤ 12297655449637^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026639321 5000000000 12297655449637 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169520459/312500000 : ℝ)^8373 ≤ (347658845373/781250000000 : ℝ)^6325 := by
    have hnat : (169520459 : ℕ)^8373*781250000000^6325 ≤ 347658845373^6325*312500000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169520459 312500000 347658845373 781250000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304667233/10000000000 : ℝ), (-1026639321/5000000000 : ℝ), (169520459/312500000 : ℝ)] ![(10800503081223/25000000000000 : ℝ), (12297655449637/100000000000000 : ℝ), (347658845373/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304667233/10000000000 : ℝ)|^8373 ≤ (10800503081223/25000000000000 : ℝ)^6325
        have hw : |(5304667233/10000000000 : ℝ)|=(5304667233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026639321/5000000000 : ℝ)|^8373 ≤ (12297655449637/100000000000000 : ℝ)^6325
        have hw : |(-1026639321/5000000000 : ℝ)|=(1026639321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169520459/312500000 : ℝ)|^8373 ≤ (347658845373/781250000000 : ℝ)^6325
        have hw : |(169520459/312500000 : ℝ)|=(169520459/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s3_6 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652333453/5000000000 : ℝ)*x 0 + (5424655049/10000000000 : ℝ)*x 1 + (-2053278593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652333453/5000000000 : ℝ)^8373 ≤ (8640401759889/20000000000000 : ℝ)^6325 := by
    have hnat : (2652333453 : ℕ)^8373*20000000000000^6325 ≤ 8640401759889^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652333453 5000000000 8640401759889 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424655049/10000000000 : ℝ)^8373 ≤ (44500336128041/100000000000000 : ℝ)^6325 := by
    have hnat : (5424655049 : ℕ)^8373*100000000000000^6325 ≤ 44500336128041^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424655049 10000000000 44500336128041 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2053278593/10000000000 : ℝ)^8373 ≤ (12297655061137/100000000000000 : ℝ)^6325 := by
    have hnat : (2053278593 : ℕ)^8373*100000000000000^6325 ≤ 12297655061137^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053278593 10000000000 12297655061137 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652333453/5000000000 : ℝ), (5424655049/10000000000 : ℝ), (-2053278593/10000000000 : ℝ)] ![(8640401759889/20000000000000 : ℝ), (44500336128041/100000000000000 : ℝ), (12297655061137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652333453/5000000000 : ℝ)|^8373 ≤ (8640401759889/20000000000000 : ℝ)^6325
        have hw : |(2652333453/5000000000 : ℝ)|=(2652333453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424655049/10000000000 : ℝ)|^8373 ≤ (44500336128041/100000000000000 : ℝ)^6325
        have hw : |(5424655049/10000000000 : ℝ)|=(5424655049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2053278593/10000000000 : ℝ)|^8373 ≤ (12297655061137/100000000000000 : ℝ)^6325
        have hw : |(-2053278593/10000000000 : ℝ)|=(2053278593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s3_7 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357353767/10000000000 : ℝ)*x 0 + (2275113959/5000000000 : ℝ)*x 1 + (4172604221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357353767/10000000000 : ℝ)^8373 ≤ (16648502331911/50000000000000 : ℝ)^6325 := by
    have hnat : (4357353767 : ℕ)^8373*50000000000000^6325 ≤ 16648502331911^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357353767 10000000000 16648502331911 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2275113959/5000000000 : ℝ)^8373 ≤ (35261937980249/100000000000000 : ℝ)^6325 := by
    have hnat : (2275113959 : ℕ)^8373*100000000000000^6325 ≤ 35261937980249^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275113959 5000000000 35261937980249 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172604221/10000000000 : ℝ)^8373 ≤ (31441057344093/100000000000000 : ℝ)^6325 := by
    have hnat : (4172604221 : ℕ)^8373*100000000000000^6325 ≤ 31441057344093^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172604221 10000000000 31441057344093 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357353767/10000000000 : ℝ), (2275113959/5000000000 : ℝ), (4172604221/10000000000 : ℝ)] ![(16648502331911/50000000000000 : ℝ), (35261937980249/100000000000000 : ℝ), (31441057344093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357353767/10000000000 : ℝ)|^8373 ≤ (16648502331911/50000000000000 : ℝ)^6325
        have hw : |(4357353767/10000000000 : ℝ)|=(4357353767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2275113959/5000000000 : ℝ)|^8373 ≤ (35261937980249/100000000000000 : ℝ)^6325
        have hw : |(2275113959/5000000000 : ℝ)|=(2275113959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172604221/10000000000 : ℝ)|^8373 ≤ (31441057344093/100000000000000 : ℝ)^6325
        have hw : |(4172604221/10000000000 : ℝ)|=(4172604221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1180_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2049/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2149/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2049/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9239/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2049/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9239/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2049/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9239/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2049/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9239/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2049/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9239/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2049/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9239/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9239/100000 : ℝ) ^ (2093/512 : ℝ) ≤ (5910007068559523/100000000000000000000 : ℝ) := by
    have hpowers : (9239/100000 : ℝ)^2093 ≤ (5910007068559523/100000000000000000000 : ℝ)^512 := by
      have hnat : (9239 : ℕ)^2093*100000000000000000000^512 ≤ 5910007068559523^512*100000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9239 100000 5910007068559523 100000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9239/100000 : ℝ)) (X := (5910007068559523/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2049/12500 : ℝ) ^ (2093/512 : ℝ) ≤ (61588736190511581/100000000000000000000 : ℝ) := by
    have hpowers : (2049/12500 : ℝ)^2093 ≤ (61588736190511581/100000000000000000000 : ℝ)^512 := by
      have hnat : (2049 : ℕ)^2093*100000000000000000000^512 ≤ 61588736190511581^512*12500^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2049 12500 61588736190511581 100000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2049/12500 : ℝ)) (X := (61588736190511581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005910007068559523/50000000000000000000 : ℝ) ≤ (500014456705891/500000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (50005910007068559523/50000000000000000000 : ℝ)^512 ≤ (500014456705891/500000000000000 : ℝ)^2093 := by
      have hnat : (50005910007068559523 : ℕ)^512*500000000000000^2093 ≤ 500014456705891^2093*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005910007068559523 50000000000000000000 500014456705891 500000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500014456705891/500000000000000 : ℝ)) (X := (50005910007068559523/50000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (781777333931711493/781250000000000000 : ℝ) ≤ (5000825383412807/5000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (781777333931711493/781250000000000000 : ℝ)^512 ≤ (5000825383412807/5000000000000000 : ℝ)^2093 := by
      have hnat : (781777333931711493 : ℕ)^512*5000000000000000^2093 ≤ 5000825383412807^2093*781250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781777333931711493 781250000000000000 5000825383412807 5000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000825383412807/5000000000000000 : ℝ)) (X := (781777333931711493/781250000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50061588736190511581/50000000000000000000 : ℝ) ≤ (312594137485419/312500000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (50061588736190511581/50000000000000000000 : ℝ)^512 ≤ (312594137485419/312500000000000 : ℝ)^2093 := by
      have hnat : (50061588736190511581 : ℕ)^512*312500000000000^2093 ≤ 312594137485419^2093*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50061588736190511581 50000000000000000000 312594137485419 312500000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312594137485419/312500000000000 : ℝ)) (X := (50061588736190511581/50000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5910007068559523/100000000000000000000 : ℝ) ≤ ((48578062450523199/48593750000000000 : ℝ)+2*(29600711039/15550000000000 : ℝ)*(9239/100000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (48578062450523199/48593750000000000 : ℝ)+2*(29600711039/15550000000000 : ℝ)*(9239/100000 : ℝ)=(500014456705891/500000000000000 : ℝ) by norm_num, show 1+2*(5910007068559523/100000000000000000000 : ℝ)=(50005910007068559523/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(61588736190511581/100000000000000000000 : ℝ)+(5910007068559523/100000000000000000000 : ℝ) ≤ ((48578062450523199/48593750000000000 : ℝ)+(29600711039/15550000000000 : ℝ)*((2049/12500 : ℝ)+(9239/100000 : ℝ)))^(2093/512 : ℝ) := by
    rw [show (48578062450523199/48593750000000000 : ℝ)+(29600711039/15550000000000 : ℝ)*((2049/12500 : ℝ)+(9239/100000 : ℝ))=(5000825383412807/5000000000000000 : ℝ) by norm_num, show 1+(61588736190511581/100000000000000000000 : ℝ)+(5910007068559523/100000000000000000000 : ℝ)=(781777333931711493/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(61588736190511581/100000000000000000000 : ℝ) ≤ ((48578062450523199/48593750000000000 : ℝ)+2*(29600711039/15550000000000 : ℝ)*(2049/12500 : ℝ))^(2093/512 : ℝ) := by
    rw [show (48578062450523199/48593750000000000 : ℝ)+2*(29600711039/15550000000000 : ℝ)*(2049/12500 : ℝ)=(312594137485419/312500000000000 : ℝ) by norm_num, show 1+2*(61588736190511581/100000000000000000000 : ℝ)=(50061588736190511581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (48578062450523199/48593750000000000 : ℝ)*(X 1 0+X 2 0)+(29600711039/15550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (9239/100000 : ℝ)) (hi := (2049/12500 : ℝ)) (c := (48578062450523199/48593750000000000 : ℝ)) (alpha := (29600711039/15550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (48578062450523199/48593750000000000 : ℝ)*(X 0 1+X 2 1)+(29600711039/15550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (9239/100000 : ℝ)) (hi := (2049/12500 : ℝ)) (c := (48578062450523199/48593750000000000 : ℝ)) (alpha := (29600711039/15550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (48578062450523199/48593750000000000 : ℝ)*(X 0 2+X 1 2)+(29600711039/15550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (9239/100000 : ℝ)) (hi := (2049/12500 : ℝ)) (c := (48578062450523199/48593750000000000 : ℝ)) (alpha := (29600711039/15550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-429087683/2000000000 : ℝ)*X 0 0+(5425376493/10000000000 : ℝ)*X 0 1+(5235531179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070579009/2000000000 : ℝ)*X 1 0+(-1121201311/5000000000 : ℝ)*X 1 1+(5235530983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352895133/10000000000 : ℝ)*X 2 0+(654441369/1250000000 : ℝ)*X 2 1+(-2242402547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871464151/2000000000 : ℝ)*X 0 0+(83423149/200000000 : ℝ)*X 0 1+(1137916767/2500000000 : ℝ)*X 0 2+(871464151/2000000000 : ℝ)*X 1 0+(83423149/200000000 : ℝ)*X 1 1+(1137916767/2500000000 : ℝ)*X 1 2+(871464151/2000000000 : ℝ)*X 2 0+(83423149/200000000 : ℝ)*X 2 1+(1137916767/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1072727373/5000000000 : ℝ)*X 0 0+(5236249049/10000000000 : ℝ)*X 0 1+(5424654729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304667233/10000000000 : ℝ)*X 1 0+(-1026639321/5000000000 : ℝ)*X 1 1+(169520459/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652333453/5000000000 : ℝ)*X 2 0+(5424655049/10000000000 : ℝ)*X 2 1+(-2053278593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357353767/10000000000 : ℝ)*X 0 0+(2275113959/5000000000 : ℝ)*X 0 1+(4172604221/10000000000 : ℝ)*X 0 2+(4357353767/10000000000 : ℝ)*X 1 0+(2275113959/5000000000 : ℝ)*X 1 1+(4172604221/10000000000 : ℝ)*X 1 2+(4357353767/10000000000 : ℝ)*X 2 0+(2275113959/5000000000 : ℝ)*X 2 1+(4172604221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2643109739614379794389/777500000000000000000000000 : ℝ) := by norm_num
    linear_combination (232781917/25000000000000 : ℝ)*(base19) + (46876579/5000000000000 : ℝ)*(base23) + (8585161/20000000000000 : ℝ)*(lower2) + (32347421/50000000000000 : ℝ)*(upper3) + (20505213/20000000000000 : ℝ)*(upper5) + (1973885284986821/50000000000000 : ℝ)*(major0) + (1973885284986821/50000000000000 : ℝ)*(major1) + (1973885284986821/50000000000000 : ℝ)*(major2) + (5267458091688619/100000000000000 : ℝ)*(sp0) + (164608491815611/3125000000000 : ℝ)*(sp1) + (131686793292391/2500000000000 : ℝ)*(sp2) + (2628061342988349/100000000000000 : ℝ)*(sp3) + (7288769301/50000000000000 : ℝ)*(sp4) + (27400059/390625000000 : ℝ)*(sp7) + (1314034178701727/50000000000000 : ℝ)*(f.failure) + (263373633461361/5000000000000 : ℝ)*(f.sum) + (4528889371673/777500000000000000000000000 : ℝ)*base65 + (44289921794063617/4859375000000000000000000000000 : ℝ)*base68 + (32575675901748883/4859375000000000000000000000000 : ℝ)*base69 + (2419865042126117/4859375000000000000000000000000 : ℝ)*base72 + (3010856149357/777500000000000000000000000 : ℝ)*base74 + (219448498129813/303710937500000000000000000000 : ℝ)*base75 + (28797730472248883/4859375000000000000000000000000 : ℝ)*base77 + (19671360719414621/2429687500000000000000000000000 : ℝ)*base80 + (126384337997/48593750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (87567271/5000000000000000000000 : ℝ)*base89 + (87567271/5000000000000000000000 : ℝ)*base91 + (87567271/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7384991439412598113072101/4859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108978659/12500000000000 : ℝ)*(base19) + (754110049/100000000000000 : ℝ)*(base23) + (6688433/25000000000000 : ℝ)*(upper3) + (103656131/100000000000000 : ℝ)*(lower4) + (112283611/100000000000000 : ℝ)*(upper5) + (994478792894067/25000000000000 : ℝ)*(major0) + (994478792894067/25000000000000 : ℝ)*(major1) + (994478792894067/25000000000000 : ℝ)*(major2) + (741052991/4000000000000 : ℝ)*(sp1) + (5018209123/25000000000000 : ℝ)*(sp2) + (2653847193771921/50000000000000 : ℝ)*(sp4) + (1061534997877959/20000000000000 : ℝ)*(sp5) + (53076735605973/1000000000000 : ℝ)*(sp6) + (20688561757427/781250000000 : ℝ)*(sp7) + (20688561757427/781250000000 : ℝ)*(f.failure) + (2653847193771921/50000000000000 : ℝ)*(f.sum) + (1484991392799/388750000000000000000000000 : ℝ)*base66 + (5559536656232459/2429687500000000000000000000000 : ℝ)*base68 + (19006951492232459/2429687500000000000000000000000 : ℝ)*base70 + (8627084660576209/2429687500000000000000000000000 : ℝ)*base72 + (78356505849/24296875000000000000000000 : ℝ)*base74 + (43548653199105543/4859375000000000000000000000000 : ℝ)*base76 + (1975235530233417/1214843750000000000000000000000 : ℝ)*base78 + (1666439140170917/1214843750000000000000000000000 : ℝ)*base80 + (50007000341/97187500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (178371/78125000000000000000 : ℝ)*base89 + (178371/78125000000000000000 : ℝ)*base91 + (178371/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1180_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2049/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1180_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1180_s4_0 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2148150859/10000000000 : ℝ)*x 0 + (5400126039/10000000000 : ℝ)*x 1 + (5259005903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148150859/10000000000 : ℝ)^8373 ≤ (13055426030647/100000000000000 : ℝ)^6325 := by
    have hnat : (2148150859 : ℕ)^8373*100000000000000^6325 ≤ 13055426030647^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148150859 10000000000 13055426030647 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400126039/10000000000 : ℝ)^8373 ≤ (5529269672751/12500000000000 : ℝ)^6325 := by
    have hnat : (5400126039 : ℕ)^8373*12500000000000^6325 ≤ 5529269672751^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400126039 10000000000 5529269672751 12500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259005903/10000000000 : ℝ)^8373 ≤ (4271041656741/10000000000000 : ℝ)^6325 := by
    have hnat : (5259005903 : ℕ)^8373*10000000000000^6325 ≤ 4271041656741^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259005903 10000000000 4271041656741 10000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2148150859/10000000000 : ℝ), (5400126039/10000000000 : ℝ), (5259005903/10000000000 : ℝ)] ![(13055426030647/100000000000000 : ℝ), (5529269672751/12500000000000 : ℝ), (4271041656741/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2148150859/10000000000 : ℝ)|^8373 ≤ (13055426030647/100000000000000 : ℝ)^6325
        have hw : |(-2148150859/10000000000 : ℝ)|=(2148150859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400126039/10000000000 : ℝ)|^8373 ≤ (5529269672751/12500000000000 : ℝ)^6325
        have hw : |(5400126039/10000000000 : ℝ)|=(5400126039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259005903/10000000000 : ℝ)|^8373 ≤ (4271041656741/10000000000000 : ℝ)^6325
        have hw : |(5259005903/10000000000 : ℝ)|=(5259005903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s4_1 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346565189/10000000000 : ℝ)*x 0 + (-2219839333/10000000000 : ℝ)*x 1 + (2629503163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346565189/10000000000 : ℝ)^8373 ≤ (8730859682549/20000000000000 : ℝ)^6325 := by
    have hnat : (5346565189 : ℕ)^8373*20000000000000^6325 ≤ 8730859682549^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346565189 10000000000 8730859682549 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219839333/10000000000 : ℝ)^8373 ≤ (3408820112501/25000000000000 : ℝ)^6325 := by
    have hnat : (2219839333 : ℕ)^8373*25000000000000^6325 ≤ 3408820112501^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219839333 10000000000 3408820112501 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629503163/5000000000 : ℝ)^8373 ≤ (42710421115103/100000000000000 : ℝ)^6325 := by
    have hnat : (2629503163 : ℕ)^8373*100000000000000^6325 ≤ 42710421115103^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629503163 5000000000 42710421115103 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346565189/10000000000 : ℝ), (-2219839333/10000000000 : ℝ), (2629503163/5000000000 : ℝ)] ![(8730859682549/20000000000000 : ℝ), (3408820112501/25000000000000 : ℝ), (42710421115103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346565189/10000000000 : ℝ)|^8373 ≤ (8730859682549/20000000000000 : ℝ)^6325
        have hw : |(5346565189/10000000000 : ℝ)|=(5346565189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2219839333/10000000000 : ℝ)|^8373 ≤ (3408820112501/25000000000000 : ℝ)^6325
        have hw : |(-2219839333/10000000000 : ℝ)|=(2219839333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629503163/5000000000 : ℝ)|^8373 ≤ (42710421115103/100000000000000 : ℝ)^6325
        have hw : |(2629503163/5000000000 : ℝ)|=(2629503163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s4_2 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673282573/5000000000 : ℝ)*x 0 + (2629503451/5000000000 : ℝ)*x 1 + (-2219838629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673282573/5000000000 : ℝ)^8373 ≤ (10913574486993/25000000000000 : ℝ)^6325 := by
    have hnat : (2673282573 : ℕ)^8373*25000000000000^6325 ≤ 10913574486993^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673282573 5000000000 10913574486993 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629503451/5000000000 : ℝ)^8373 ≤ (8542085461541/20000000000000 : ℝ)^6325 := by
    have hnat : (2629503451 : ℕ)^8373*20000000000000^6325 ≤ 8542085461541^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629503451 5000000000 8542085461541 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219838629/10000000000 : ℝ)^8373 ≤ (1704409340691/12500000000000 : ℝ)^6325 := by
    have hnat : (2219838629 : ℕ)^8373*12500000000000^6325 ≤ 1704409340691^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219838629 10000000000 1704409340691 12500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673282573/5000000000 : ℝ), (2629503451/5000000000 : ℝ), (-2219838629/10000000000 : ℝ)] ![(10913574486993/25000000000000 : ℝ), (8542085461541/20000000000000 : ℝ), (1704409340691/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673282573/5000000000 : ℝ)|^8373 ≤ (10913574486993/25000000000000 : ℝ)^6325
        have hw : |(2673282573/5000000000 : ℝ)|=(2673282573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629503451/5000000000 : ℝ)|^8373 ≤ (8542085461541/20000000000000 : ℝ)^6325
        have hw : |(2629503451/5000000000 : ℝ)|=(2629503451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2219838629/10000000000 : ℝ)|^8373 ≤ (1704409340691/12500000000000 : ℝ)^6325
        have hw : |(-2219838629/10000000000 : ℝ)|=(2219838629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s4_3 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089735529/2500000000 : ℝ)*x 0 + (4219778973/10000000000 : ℝ)*x 1 + (562828409/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089735529/2500000000 : ℝ)^8373 ≤ (4164134141459/12500000000000 : ℝ)^6325 := by
    have hnat : (1089735529 : ℕ)^8373*12500000000000^6325 ≤ 4164134141459^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089735529 2500000000 4164134141459 12500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4219778973/10000000000 : ℝ)^8373 ≤ (7978120508099/25000000000000 : ℝ)^6325 := by
    have hnat : (4219778973 : ℕ)^8373*25000000000000^6325 ≤ 7978120508099^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219778973 10000000000 7978120508099 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562828409/1250000000 : ℝ)^8373 ≤ (34774444815361/100000000000000 : ℝ)^6325 := by
    have hnat : (562828409 : ℕ)^8373*100000000000000^6325 ≤ 34774444815361^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562828409 1250000000 34774444815361 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089735529/2500000000 : ℝ), (4219778973/10000000000 : ℝ), (562828409/1250000000 : ℝ)] ![(4164134141459/12500000000000 : ℝ), (7978120508099/25000000000000 : ℝ), (34774444815361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089735529/2500000000 : ℝ)|^8373 ≤ (4164134141459/12500000000000 : ℝ)^6325
        have hw : |(1089735529/2500000000 : ℝ)|=(1089735529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4219778973/10000000000 : ℝ)|^8373 ≤ (7978120508099/25000000000000 : ℝ)^6325
        have hw : |(4219778973/10000000000 : ℝ)|=(4219778973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562828409/1250000000 : ℝ)|^8373 ≤ (34774444815361/100000000000000 : ℝ)^6325
        have hw : |(562828409/1250000000 : ℝ)|=(562828409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s4_4 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2148157619/10000000000 : ℝ)*x 0 + (2629701737/5000000000 : ℝ)*x 1 + (5399726837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148157619/10000000000 : ℝ)^8373 ≤ (6527740208739/50000000000000 : ℝ)^6325 := by
    have hnat : (2148157619 : ℕ)^8373*50000000000000^6325 ≤ 6527740208739^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148157619 10000000000 6527740208739 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629701737/5000000000 : ℝ)^8373 ≤ (42714690923737/100000000000000 : ℝ)^6325 := by
    have hnat : (2629701737 : ℕ)^8373*100000000000000^6325 ≤ 42714690923737^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629701737 5000000000 42714690923737 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399726837/10000000000 : ℝ)^8373 ≤ (44229828637691/100000000000000 : ℝ)^6325 := by
    have hnat : (5399726837 : ℕ)^8373*100000000000000^6325 ≤ 44229828637691^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399726837 10000000000 44229828637691 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2148157619/10000000000 : ℝ), (2629701737/5000000000 : ℝ), (5399726837/10000000000 : ℝ)] ![(6527740208739/50000000000000 : ℝ), (42714690923737/100000000000000 : ℝ), (44229828637691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2148157619/10000000000 : ℝ)|^8373 ≤ (6527740208739/50000000000000 : ℝ)^6325
        have hw : |(-2148157619/10000000000 : ℝ)|=(2148157619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629701737/5000000000 : ℝ)|^8373 ≤ (42714690923737/100000000000000 : ℝ)^6325
        have hw : |(2629701737/5000000000 : ℝ)|=(2629701737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399726837/10000000000 : ℝ)|^8373 ≤ (44229828637691/100000000000000 : ℝ)^6325
        have hw : |(5399726837/10000000000 : ℝ)|=(5399726837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s4_5 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062143013/2000000000 : ℝ)*x 0 + (-103955913/500000000 : ℝ)*x 1 + (674965869/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062143013/2000000000 : ℝ)^8373 ≤ (21633613568283/50000000000000 : ℝ)^6325 := by
    have hnat : (1062143013 : ℕ)^8373*50000000000000^6325 ≤ 21633613568283^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062143013 2000000000 21633613568283 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103955913/500000000 : ℝ)^8373 ≤ (2500588591647/20000000000000 : ℝ)^6325 := by
    have hnat : (103955913 : ℕ)^8373*20000000000000^6325 ≤ 2500588591647^6325*500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103955913 500000000 2500588591647 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674965869/1250000000 : ℝ)^8373 ≤ (22114914942339/50000000000000 : ℝ)^6325 := by
    have hnat : (674965869 : ℕ)^8373*50000000000000^6325 ≤ 22114914942339^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674965869 1250000000 22114914942339 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062143013/2000000000 : ℝ), (-103955913/500000000 : ℝ), (674965869/1250000000 : ℝ)] ![(21633613568283/50000000000000 : ℝ), (2500588591647/20000000000000 : ℝ), (22114914942339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062143013/2000000000 : ℝ)|^8373 ≤ (21633613568283/50000000000000 : ℝ)^6325
        have hw : |(1062143013/2000000000 : ℝ)|=(1062143013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103955913/500000000 : ℝ)|^8373 ≤ (2500588591647/20000000000000 : ℝ)^6325
        have hw : |(-103955913/500000000 : ℝ)|=(103955913/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674965869/1250000000 : ℝ)|^8373 ≤ (22114914942339/50000000000000 : ℝ)^6325
        have hw : |(674965869/1250000000 : ℝ)|=(674965869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s4_6 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310715169/10000000000 : ℝ)*x 0 + (5399726741/10000000000 : ℝ)*x 1 + (-2079118407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310715169/10000000000 : ℝ)^8373 ≤ (43267228258223/100000000000000 : ℝ)^6325 := by
    have hnat : (5310715169 : ℕ)^8373*100000000000000^6325 ≤ 43267228258223^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310715169 10000000000 43267228258223 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399726741/10000000000 : ℝ)^8373 ≤ (5528728449591/12500000000000 : ℝ)^6325 := by
    have hnat : (5399726741 : ℕ)^8373*12500000000000^6325 ≤ 5528728449591^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399726741 10000000000 5528728449591 12500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079118407/10000000000 : ℝ)^8373 ≤ (781434008029/6250000000000 : ℝ)^6325 := by
    have hnat : (2079118407 : ℕ)^8373*6250000000000^6325 ≤ 781434008029^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079118407 10000000000 781434008029 6250000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310715169/10000000000 : ℝ), (5399726741/10000000000 : ℝ), (-2079118407/10000000000 : ℝ)] ![(43267228258223/100000000000000 : ℝ), (5528728449591/12500000000000 : ℝ), (781434008029/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310715169/10000000000 : ℝ)|^8373 ≤ (43267228258223/100000000000000 : ℝ)^6325
        have hw : |(5310715169/10000000000 : ℝ)|=(5310715169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399726741/10000000000 : ℝ)|^8373 ≤ (5528728449591/12500000000000 : ℝ)^6325
        have hw : |(5399726741/10000000000 : ℝ)|=(5399726741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2079118407/10000000000 : ℝ)|^8373 ≤ (781434008029/6250000000000 : ℝ)^6325
        have hw : |(-2079118407/10000000000 : ℝ)|=(2079118407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s4_7 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358954737/10000000000 : ℝ)*x 0 + (4501830889/10000000000 : ℝ)*x 1 + (2110289731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358954737/10000000000 : ℝ)^8373 ≤ (33313200819097/100000000000000 : ℝ)^6325 := by
    have hnat : (4358954737 : ℕ)^8373*100000000000000^6325 ≤ 33313200819097^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358954737 10000000000 33313200819097 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501830889/10000000000 : ℝ)^8373 ≤ (34766302942563/100000000000000 : ℝ)^6325 := by
    have hnat : (4501830889 : ℕ)^8373*100000000000000^6325 ≤ 34766302942563^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501830889 10000000000 34766302942563 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110289731/5000000000 : ℝ)^8373 ≤ (6384099246369/20000000000000 : ℝ)^6325 := by
    have hnat : (2110289731 : ℕ)^8373*20000000000000^6325 ≤ 6384099246369^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110289731 5000000000 6384099246369 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358954737/10000000000 : ℝ), (4501830889/10000000000 : ℝ), (2110289731/5000000000 : ℝ)] ![(33313200819097/100000000000000 : ℝ), (34766302942563/100000000000000 : ℝ), (6384099246369/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358954737/10000000000 : ℝ)|^8373 ≤ (33313200819097/100000000000000 : ℝ)^6325
        have hw : |(4358954737/10000000000 : ℝ)|=(4358954737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501830889/10000000000 : ℝ)|^8373 ≤ (34766302942563/100000000000000 : ℝ)^6325
        have hw : |(4501830889/10000000000 : ℝ)|=(4501830889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2110289731/5000000000 : ℝ)|^8373 ≤ (6384099246369/20000000000000 : ℝ)^6325
        have hw : |(2110289731/5000000000 : ℝ)|=(2110289731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1180_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5623/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2149/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2149/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2149/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2149/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2149/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2149/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2149/20000 : ℝ) ^ (2093/512 : ℝ) ≤ (684790652302789/6250000000000000000 : ℝ) := by
    have hpowers : (2149/20000 : ℝ)^2093 ≤ (684790652302789/6250000000000000000 : ℝ)^512 := by
      have hnat : (2149 : ℕ)^2093*6250000000000000000^512 ≤ 684790652302789^512*20000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2149 20000 684790652302789 6250000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2149/20000 : ℝ)) (X := (684790652302789/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7381/50000 : ℝ) ^ (2093/512 : ℝ) ≤ (1254314601921593/3125000000000000000 : ℝ) := by
    have hpowers : (7381/50000 : ℝ)^2093 ≤ (1254314601921593/3125000000000000000 : ℝ)^512 := by
      have hnat : (7381 : ℕ)^2093*3125000000000000000^512 ≤ 1254314601921593^512*50000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7381 50000 1254314601921593 3125000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7381/50000 : ℝ)) (X := (1254314601921593/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125684790652302789/3125000000000000000 : ℝ) ≤ (1000053600963157/1000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (3125684790652302789/3125000000000000000 : ℝ)^512 ≤ (1000053600963157/1000000000000000 : ℝ)^2093 := by
      have hnat : (3125684790652302789 : ℕ)^512*1000000000000000^2093 ≤ 1000053600963157^2093*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125684790652302789 3125000000000000000 1000053600963157 1000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000053600963157/1000000000000000 : ℝ)) (X := (3125684790652302789/3125000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (250127736794245839/250000000000000000 : ℝ) ≤ (10001249663094141/10000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (250127736794245839/250000000000000000 : ℝ)^512 ≤ (10001249663094141/10000000000000000 : ℝ)^2093 := by
      have hnat : (250127736794245839 : ℕ)^512*10000000000000000^2093 ≤ 10001249663094141^2093*250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250127736794245839 250000000000000000 10001249663094141 10000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001249663094141/10000000000000000 : ℝ)) (X := (250127736794245839/250000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563754314601921593/1562500000000000000 : ℝ) ≤ (1250245414569589/1250000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (1563754314601921593/1562500000000000000 : ℝ)^512 ≤ (1250245414569589/1250000000000000 : ℝ)^2093 := by
      have hnat : (1563754314601921593 : ℕ)^512*1250000000000000^2093 ≤ 1250245414569589^2093*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563754314601921593 1562500000000000000 1250245414569589 1250000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250245414569589/1250000000000000 : ℝ)) (X := (1563754314601921593/1562500000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(684790652302789/6250000000000000000 : ℝ) ≤ ((401568167377793659/401700000000000000 : ℝ)+2*(713653462571/401700000000000 : ℝ)*(2149/20000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (401568167377793659/401700000000000000 : ℝ)+2*(713653462571/401700000000000 : ℝ)*(2149/20000 : ℝ)=(1000053600963157/1000000000000000 : ℝ) by norm_num, show 1+2*(684790652302789/6250000000000000000 : ℝ)=(3125684790652302789/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1254314601921593/3125000000000000000 : ℝ)+(684790652302789/6250000000000000000 : ℝ) ≤ ((401568167377793659/401700000000000000 : ℝ)+(713653462571/401700000000000 : ℝ)*((7381/50000 : ℝ)+(2149/20000 : ℝ)))^(2093/512 : ℝ) := by
    rw [show (401568167377793659/401700000000000000 : ℝ)+(713653462571/401700000000000 : ℝ)*((7381/50000 : ℝ)+(2149/20000 : ℝ))=(10001249663094141/10000000000000000 : ℝ) by norm_num, show 1+(1254314601921593/3125000000000000000 : ℝ)+(684790652302789/6250000000000000000 : ℝ)=(250127736794245839/250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1254314601921593/3125000000000000000 : ℝ) ≤ ((401568167377793659/401700000000000000 : ℝ)+2*(713653462571/401700000000000 : ℝ)*(7381/50000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (401568167377793659/401700000000000000 : ℝ)+2*(713653462571/401700000000000 : ℝ)*(7381/50000 : ℝ)=(1250245414569589/1250000000000000 : ℝ) by norm_num, show 1+2*(1254314601921593/3125000000000000000 : ℝ)=(1563754314601921593/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (401568167377793659/401700000000000000 : ℝ)*(X 1 0+X 2 0)+(713653462571/401700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (2149/20000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (401568167377793659/401700000000000000 : ℝ)) (alpha := (713653462571/401700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (401568167377793659/401700000000000000 : ℝ)*(X 0 1+X 2 1)+(713653462571/401700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (2149/20000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (401568167377793659/401700000000000000 : ℝ)) (alpha := (713653462571/401700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (401568167377793659/401700000000000000 : ℝ)*(X 0 2+X 1 2)+(713653462571/401700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (2149/20000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (401568167377793659/401700000000000000 : ℝ)) (alpha := (713653462571/401700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2148150859/10000000000 : ℝ)*X 0 0+(5400126039/10000000000 : ℝ)*X 0 1+(5259005903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346565189/10000000000 : ℝ)*X 1 0+(-2219839333/10000000000 : ℝ)*X 1 1+(2629503163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673282573/5000000000 : ℝ)*X 2 0+(2629503451/5000000000 : ℝ)*X 2 1+(-2219838629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089735529/2500000000 : ℝ)*X 0 0+(4219778973/10000000000 : ℝ)*X 0 1+(562828409/1250000000 : ℝ)*X 0 2+(1089735529/2500000000 : ℝ)*X 1 0+(4219778973/10000000000 : ℝ)*X 1 1+(562828409/1250000000 : ℝ)*X 1 2+(1089735529/2500000000 : ℝ)*X 2 0+(4219778973/10000000000 : ℝ)*X 2 1+(562828409/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2148157619/10000000000 : ℝ)*X 0 0+(2629701737/5000000000 : ℝ)*X 0 1+(5399726837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062143013/2000000000 : ℝ)*X 1 0+(-103955913/500000000 : ℝ)*X 1 1+(674965869/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310715169/10000000000 : ℝ)*X 2 0+(5399726741/10000000000 : ℝ)*X 2 1+(-2079118407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358954737/10000000000 : ℝ)*X 0 0+(4501830889/10000000000 : ℝ)*X 0 1+(2110289731/5000000000 : ℝ)*X 0 2+(4358954737/10000000000 : ℝ)*X 1 0+(4501830889/10000000000 : ℝ)*X 1 1+(2110289731/5000000000 : ℝ)*X 1 2+(4358954737/10000000000 : ℝ)*X 2 0+(4501830889/10000000000 : ℝ)*X 2 1+(2110289731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60299109541682509286671/26152343750000000000000000000 : ℝ) := by norm_num
    linear_combination (390750263/50000000000000 : ℝ)*(base19) + (282288081/50000000000000 : ℝ)*(base23) + (62629251/50000000000000 : ℝ)*(lower2) + (536672581/100000000000000 : ℝ)*(upper5) + (331929716697577/6250000000000 : ℝ)*(major0) + (331929716697577/6250000000000 : ℝ)*(major1) + (331929716697577/6250000000000 : ℝ)*(major2) + (1417238381552761/20000000000000 : ℝ)*(sp0) + (7086238756487523/100000000000000 : ℝ)*(sp1) + (1417250012211849/20000000000000 : ℝ)*(sp2) + (55241974879597/1562500000000 : ℝ)*(sp3) + (58717871601/100000000000000 : ℝ)*(sp4) + (2771911839/25000000000000 : ℝ)*(sp5) + (1729942077/12500000000000 : ℝ)*(sp7) + (441937528978853/12500000000000 : ℝ)*(f.failure) + (7086250625635407/100000000000000 : ℝ)*(f.sum) + (13774170765481/10042500000000000000000000000 : ℝ)*base65 + (6918735971868647/418437500000000000000000000000 : ℝ)*base68 + (5751115238597919/836875000000000000000000000000 : ℝ)*base70 + (479301042707057/104609375000000000000000000000 : ℝ)*base71 + (6590052097907/20085000000000000000000000000 : ℝ)*base73 + (7422532414386669/836875000000000000000000000000 : ℝ)*base76 + (16130767714241669/836875000000000000000000000000 : ℝ)*base78 + (19744427529624169/836875000000000000000000000000 : ℝ)*base80 + (18365334927883/20085000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/50000000000000 : ℝ)*base86 + (6163069/1250000000000000000000 : ℝ)*base89 + (6163069/1250000000000000000000 : ℝ)*base91 + (6163069/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1327382863370320119463243/515000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132884133/12500000000000 : ℝ)*(base19) + (1551475771/100000000000000 : ℝ)*(base23) + (202166953/100000000000000 : ℝ)*(upper2) + (94073/390625000000 : ℝ)*(upper3) + (22817807/10000000000000 : ℝ)*(upper5) + (5340967079523167/100000000000000 : ℝ)*(major0) + (5340967079523167/100000000000000 : ℝ)*(major1) + (5340967079523167/100000000000000 : ℝ)*(major2) + (38865202807/100000000000000 : ℝ)*(sp1) + (34149947211/100000000000000 : ℝ)*(sp2) + (7126401569194279/100000000000000 : ℝ)*(sp4) + (890795205114801/12500000000000 : ℝ)*(sp5) + (7126365867771297/100000000000000 : ℝ)*(sp6) + (35555325039373/1000000000000 : ℝ)*(sp7) + (35555325039373/1000000000000 : ℝ)*(f.failure) + (7126401569194279/100000000000000 : ℝ)*(f.sum) + (10634707494221/10042500000000000000000000000 : ℝ)*base65 + (139937468387421649/13390000000000000000000000000000 : ℝ)*base68 + (177380101827451649/13390000000000000000000000000000 : ℝ)*base70 + (40183403755251649/13390000000000000000000000000000 : ℝ)*base72 + (60144133069/627656250000000000000000000 : ℝ)*base74 + (126676509852701649/13390000000000000000000000000000 : ℝ)*base76 + (42064832066091649/13390000000000000000000000000000 : ℝ)*base78 + (82551652856091649/13390000000000000000000000000000 : ℝ)*base80 + (73275231332813/20085000000000000000000000000 : ℝ)*base82 + (306971/100000000000000000000 : ℝ)*base90 + (306971/100000000000000000000 : ℝ)*base92 + (306971/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1180_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1180_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1180_s5_0 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-268588459/1250000000 : ℝ)*x 0 + (5393931717/10000000000 : ℝ)*x 1 + (5264834659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268588459/1250000000 : ℝ)^8373 ≤ (3264976498399/25000000000000 : ℝ)^6325 := by
    have hnat : (268588459 : ℕ)^8373*25000000000000^6325 ≤ 3264976498399^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268588459 1250000000 3264976498399 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393931717/10000000000 : ℝ)^8373 ≤ (44167000964369/100000000000000 : ℝ)^6325 := by
    have hnat : (5393931717 : ℕ)^8373*100000000000000^6325 ≤ 44167000964369^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393931717 10000000000 44167000964369 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264834659/10000000000 : ℝ)^8373 ≤ (21386546515763/50000000000000 : ℝ)^6325 := by
    have hnat : (5264834659 : ℕ)^8373*50000000000000^6325 ≤ 21386546515763^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264834659 10000000000 21386546515763 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268588459/1250000000 : ℝ), (5393931717/10000000000 : ℝ), (5264834659/10000000000 : ℝ)] ![(3264976498399/25000000000000 : ℝ), (44167000964369/100000000000000 : ℝ), (21386546515763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268588459/1250000000 : ℝ)|^8373 ≤ (3264976498399/25000000000000 : ℝ)^6325
        have hw : |(-268588459/1250000000 : ℝ)|=(268588459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393931717/10000000000 : ℝ)|^8373 ≤ (44167000964369/100000000000000 : ℝ)^6325
        have hw : |(5393931717/10000000000 : ℝ)|=(5393931717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264834659/10000000000 : ℝ)|^8373 ≤ (21386546515763/50000000000000 : ℝ)^6325
        have hw : |(5264834659/10000000000 : ℝ)|=(5264834659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s5_1 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345006883/10000000000 : ℝ)*x 0 + (-276775109/1250000000 : ℝ)*x 1 + (263241733/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345006883/10000000000 : ℝ)^8373 ≤ (8727491194959/20000000000000 : ℝ)^6325 := by
    have hnat : (5345006883 : ℕ)^8373*20000000000000^6325 ≤ 8727491194959^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345006883 10000000000 8727491194959 20000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276775109/1250000000 : ℝ)^8373 ≤ (271789019371/2000000000000 : ℝ)^6325 := by
    have hnat : (276775109 : ℕ)^8373*2000000000000^6325 ≤ 271789019371^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276775109 1250000000 271789019371 2000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263241733/500000000 : ℝ)^8373 ≤ (42773093042281/100000000000000 : ℝ)^6325 := by
    have hnat : (263241733 : ℕ)^8373*100000000000000^6325 ≤ 42773093042281^6325*500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263241733 500000000 42773093042281 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345006883/10000000000 : ℝ), (-276775109/1250000000 : ℝ), (263241733/500000000 : ℝ)] ![(8727491194959/20000000000000 : ℝ), (271789019371/2000000000000 : ℝ), (42773093042281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345006883/10000000000 : ℝ)|^8373 ≤ (8727491194959/20000000000000 : ℝ)^6325
        have hw : |(5345006883/10000000000 : ℝ)|=(5345006883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276775109/1250000000 : ℝ)|^8373 ≤ (271789019371/2000000000000 : ℝ)^6325
        have hw : |(-276775109/1250000000 : ℝ)|=(276775109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263241733/500000000 : ℝ)|^8373 ≤ (42773093042281/100000000000000 : ℝ)^6325
        have hw : |(263241733/500000000 : ℝ)|=(263241733/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s5_2 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672503441/5000000000 : ℝ)*x 0 + (2632417331/5000000000 : ℝ)*x 1 + (-2214200871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672503441/5000000000 : ℝ)^8373 ≤ (43637455963987/100000000000000 : ℝ)^6325 := by
    have hnat : (2672503441 : ℕ)^8373*100000000000000^6325 ≤ 43637455963987^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672503441 5000000000 43637455963987 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632417331/5000000000 : ℝ)^8373 ≤ (42773093063791/100000000000000 : ℝ)^6325 := by
    have hnat : (2632417331 : ℕ)^8373*100000000000000^6325 ≤ 42773093063791^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632417331 5000000000 42773093063791 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214200871/10000000000 : ℝ)^8373 ≤ (6794725480213/50000000000000 : ℝ)^6325 := by
    have hnat : (2214200871 : ℕ)^8373*50000000000000^6325 ≤ 6794725480213^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214200871 10000000000 6794725480213 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672503441/5000000000 : ℝ), (2632417331/5000000000 : ℝ), (-2214200871/10000000000 : ℝ)] ![(43637455963987/100000000000000 : ℝ), (42773093063791/100000000000000 : ℝ), (6794725480213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672503441/5000000000 : ℝ)|^8373 ≤ (43637455963987/100000000000000 : ℝ)^6325
        have hw : |(2672503441/5000000000 : ℝ)|=(2672503441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632417331/5000000000 : ℝ)|^8373 ≤ (42773093063791/100000000000000 : ℝ)^6325
        have hw : |(2632417331/5000000000 : ℝ)|=(2632417331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2214200871/10000000000 : ℝ)|^8373 ≤ (6794725480213/50000000000000 : ℝ)^6325
        have hw : |(-2214200871/10000000000 : ℝ)|=(2214200871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s5_3 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87185359/200000000 : ℝ)*x 0 + (423178589/1000000000 : ℝ)*x 1 + (4490536851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87185359/200000000 : ℝ)^8373 ≤ (33316369652419/100000000000000 : ℝ)^6325 := by
    have hnat : (87185359 : ℕ)^8373*100000000000000^6325 ≤ 33316369652419^6325*200000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87185359 200000000 33316369652419 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423178589/1000000000 : ℝ)^8373 ≤ (4004092810753/12500000000000 : ℝ)^6325 := by
    have hnat : (423178589 : ℕ)^8373*12500000000000^6325 ≤ 4004092810753^6325*1000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423178589 1000000000 4004092810753 12500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490536851/10000000000 : ℝ)^8373 ≤ (34650887848541/100000000000000 : ℝ)^6325 := by
    have hnat : (4490536851 : ℕ)^8373*100000000000000^6325 ≤ 34650887848541^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490536851 10000000000 34650887848541 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87185359/200000000 : ℝ), (423178589/1000000000 : ℝ), (4490536851/10000000000 : ℝ)] ![(33316369652419/100000000000000 : ℝ), (4004092810753/12500000000000 : ℝ), (34650887848541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87185359/200000000 : ℝ)|^8373 ≤ (33316369652419/100000000000000 : ℝ)^6325
        have hw : |(87185359/200000000 : ℝ)|=(87185359/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423178589/1000000000 : ℝ)|^8373 ≤ (4004092810753/12500000000000 : ℝ)^6325
        have hw : |(423178589/1000000000 : ℝ)|=(423178589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490536851/10000000000 : ℝ)|^8373 ≤ (34650887848541/100000000000000 : ℝ)^6325
        have hw : |(4490536851/10000000000 : ℝ)|=(4490536851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s5_4 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-134294551/625000000 : ℝ)*x 0 + (1053033491/2000000000 : ℝ)*x 1 + (21068741/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134294551/625000000 : ℝ)^8373 ≤ (6529973691273/50000000000000 : ℝ)^6325 := by
    have hnat : (134294551 : ℕ)^8373*50000000000000^6325 ≤ 6529973691273^6325*625000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134294551 625000000 6529973691273 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053033491/2000000000 : ℝ)^8373 ≤ (21388336128357/50000000000000 : ℝ)^6325 := by
    have hnat : (1053033491 : ℕ)^8373*50000000000000^6325 ≤ 21388336128357^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053033491 2000000000 21388336128357 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21068741/39062500 : ℝ)^8373 ≤ (22081690174271/50000000000000 : ℝ)^6325 := by
    have hnat : (21068741 : ℕ)^8373*50000000000000^6325 ≤ 22081690174271^6325*39062500^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21068741 39062500 22081690174271 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-134294551/625000000 : ℝ), (1053033491/2000000000 : ℝ), (21068741/39062500 : ℝ)] ![(6529973691273/50000000000000 : ℝ), (21388336128357/50000000000000 : ℝ), (22081690174271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-134294551/625000000 : ℝ)|^8373 ≤ (6529973691273/50000000000000 : ℝ)^6325
        have hw : |(-134294551/625000000 : ℝ)|=(134294551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053033491/2000000000 : ℝ)|^8373 ≤ (21388336128357/50000000000000 : ℝ)^6325
        have hw : |(1053033491/2000000000 : ℝ)|=(1053033491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21068741/39062500 : ℝ)|^8373 ≤ (22081690174271/50000000000000 : ℝ)^6325
        have hw : |(21068741/39062500 : ℝ)|=(21068741/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s5_5 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312209539/10000000000 : ℝ)*x 0 + (-2085437587/10000000000 : ℝ)*x 1 + (134839941/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312209539/10000000000 : ℝ)^8373 ≤ (21641673006613/50000000000000 : ℝ)^6325 := by
    have hnat : (5312209539 : ℕ)^8373*50000000000000^6325 ≤ 21641673006613^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312209539 10000000000 21641673006613 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085437587/10000000000 : ℝ)^8373 ≤ (12553274235779/100000000000000 : ℝ)^6325 := by
    have hnat : (2085437587 : ℕ)^8373*100000000000000^6325 ≤ 12553274235779^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085437587 10000000000 12553274235779 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134839941/250000000 : ℝ)^8373 ≤ (44163379741537/100000000000000 : ℝ)^6325 := by
    have hnat : (134839941 : ℕ)^8373*100000000000000^6325 ≤ 44163379741537^6325*250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134839941 250000000 44163379741537 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312209539/10000000000 : ℝ), (-2085437587/10000000000 : ℝ), (134839941/250000000 : ℝ)] ![(21641673006613/50000000000000 : ℝ), (12553274235779/100000000000000 : ℝ), (44163379741537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312209539/10000000000 : ℝ)|^8373 ≤ (21641673006613/50000000000000 : ℝ)^6325
        have hw : |(5312209539/10000000000 : ℝ)|=(5312209539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2085437587/10000000000 : ℝ)|^8373 ≤ (12553274235779/100000000000000 : ℝ)^6325
        have hw : |(-2085437587/10000000000 : ℝ)|=(2085437587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134839941/250000000 : ℝ)|^8373 ≤ (44163379741537/100000000000000 : ℝ)^6325
        have hw : |(134839941/250000000 : ℝ)|=(134839941/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s5_6 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312209163/10000000000 : ℝ)*x 0 + (1348399493/2500000000 : ℝ)*x 1 + (-521359411/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312209163/10000000000 : ℝ)^8373 ≤ (10820835489409/25000000000000 : ℝ)^6325 := by
    have hnat : (5312209163 : ℕ)^8373*25000000000000^6325 ≤ 10820835489409^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312209163 10000000000 10820835489409 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348399493/2500000000 : ℝ)^8373 ≤ (4416338334021/10000000000000 : ℝ)^6325 := by
    have hnat : (1348399493 : ℕ)^8373*10000000000000^6325 ≤ 4416338334021^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348399493 2500000000 4416338334021 10000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521359411/2500000000 : ℝ)^8373 ≤ (3138318672497/25000000000000 : ℝ)^6325 := by
    have hnat : (521359411 : ℕ)^8373*25000000000000^6325 ≤ 3138318672497^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521359411 2500000000 3138318672497 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312209163/10000000000 : ℝ), (1348399493/2500000000 : ℝ), (-521359411/2500000000 : ℝ)] ![(10820835489409/25000000000000 : ℝ), (4416338334021/10000000000000 : ℝ), (3138318672497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312209163/10000000000 : ℝ)|^8373 ≤ (10820835489409/25000000000000 : ℝ)^6325
        have hw : |(5312209163/10000000000 : ℝ)|=(5312209163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348399493/2500000000 : ℝ)|^8373 ≤ (4416338334021/10000000000000 : ℝ)^6325
        have hw : |(1348399493/2500000000 : ℝ)|=(1348399493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-521359411/2500000000 : ℝ)|^8373 ≤ (3138318672497/25000000000000 : ℝ)^6325
        have hw : |(-521359411/2500000000 : ℝ)|=(521359411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s5_7 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359278271/10000000000 : ℝ)*x 0 + (280616867/625000000 : ℝ)*x 1 + (1058113839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359278271/10000000000 : ℝ)^8373 ≤ (16658237036561/50000000000000 : ℝ)^6325 := by
    have hnat : (4359278271 : ℕ)^8373*50000000000000^6325 ≤ 16658237036561^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359278271 10000000000 16658237036561 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280616867/625000000 : ℝ)^8373 ≤ (17322037424341/50000000000000 : ℝ)^6325 := by
    have hnat : (280616867 : ℕ)^8373*50000000000000^6325 ≤ 17322037424341^6325*625000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280616867 625000000 17322037424341 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058113839/2500000000 : ℝ)^8373 ≤ (32039451066683/100000000000000 : ℝ)^6325 := by
    have hnat : (1058113839 : ℕ)^8373*100000000000000^6325 ≤ 32039451066683^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058113839 2500000000 32039451066683 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359278271/10000000000 : ℝ), (280616867/625000000 : ℝ), (1058113839/2500000000 : ℝ)] ![(16658237036561/50000000000000 : ℝ), (17322037424341/50000000000000 : ℝ), (32039451066683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359278271/10000000000 : ℝ)|^8373 ≤ (16658237036561/50000000000000 : ℝ)^6325
        have hw : |(4359278271/10000000000 : ℝ)|=(4359278271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280616867/625000000 : ℝ)|^8373 ≤ (17322037424341/50000000000000 : ℝ)^6325
        have hw : |(280616867/625000000 : ℝ)|=(280616867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058113839/2500000000 : ℝ)|^8373 ≤ (32039451066683/100000000000000 : ℝ)^6325
        have hw : |(1058113839/2500000000 : ℝ)|=(1058113839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1180_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1137/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1763/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5623/50000 : ℝ) ^ (2093/512 : ℝ) ≤ (13200304356278519/100000000000000000000 : ℝ) := by
    have hpowers : (5623/50000 : ℝ)^2093 ≤ (13200304356278519/100000000000000000000 : ℝ)^512 := by
      have hnat : (5623 : ℕ)^2093*100000000000000000000^512 ≤ 13200304356278519^512*50000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5623 50000 13200304356278519 100000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5623/50000 : ℝ)) (X := (13200304356278519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (2093/512 : ℝ) ≤ (17292716744624677/50000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^2093 ≤ (17292716744624677/50000000000000000000 : ℝ)^512 := by
      have hnat : (7117 : ℕ)^2093*50000000000000000000^512 ≤ 17292716744624677^512*50000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 17292716744624677 50000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (17292716744624677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013200304356278519/50000000000000000000 : ℝ) ≤ (5000322880173277/5000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (50013200304356278519/50000000000000000000 : ℝ)^512 ≤ (5000322880173277/5000000000000000 : ℝ)^2093 := by
      have hnat : (50013200304356278519 : ℕ)^512*5000000000000000^2093 ≤ 5000322880173277^2093*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013200304356278519 50000000000000000000 5000322880173277 5000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000322880173277/5000000000000000 : ℝ)) (X := (50013200304356278519/50000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047785737845527873/100000000000000000000 : ℝ) ≤ (80009349979289/80000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (100047785737845527873/100000000000000000000 : ℝ)^512 ≤ (80009349979289/80000000000000 : ℝ)^2093 := by
      have hnat : (100047785737845527873 : ℕ)^512*80000000000000^2093 ≤ 80009349979289^2093*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047785737845527873 100000000000000000000 80009349979289 80000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80009349979289/80000000000000 : ℝ)) (X := (100047785737845527873/100000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017292716744624677/25000000000000000000 : ℝ) ≤ (625105733404731/625000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (25017292716744624677/25000000000000000000 : ℝ)^512 ≤ (625105733404731/625000000000000 : ℝ)^2093 := by
      have hnat : (25017292716744624677 : ℕ)^512*625000000000000^2093 ≤ 625105733404731^2093*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017292716744624677 25000000000000000000 625105733404731 625000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625105733404731/625000000000000 : ℝ)) (X := (25017292716744624677/25000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13200304356278519/100000000000000000000 : ℝ) ≤ ((1493508325342958621/1494000000000000000 : ℝ)+2*(522987064571/298800000000000 : ℝ)*(5623/50000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (1493508325342958621/1494000000000000000 : ℝ)+2*(522987064571/298800000000000 : ℝ)*(5623/50000 : ℝ)=(5000322880173277/5000000000000000 : ℝ) by norm_num, show 1+2*(13200304356278519/100000000000000000000 : ℝ)=(50013200304356278519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17292716744624677/50000000000000000000 : ℝ)+(13200304356278519/100000000000000000000 : ℝ) ≤ ((1493508325342958621/1494000000000000000 : ℝ)+(522987064571/298800000000000 : ℝ)*((7117/50000 : ℝ)+(5623/50000 : ℝ)))^(2093/512 : ℝ) := by
    rw [show (1493508325342958621/1494000000000000000 : ℝ)+(522987064571/298800000000000 : ℝ)*((7117/50000 : ℝ)+(5623/50000 : ℝ))=(80009349979289/80000000000000 : ℝ) by norm_num, show 1+(17292716744624677/50000000000000000000 : ℝ)+(13200304356278519/100000000000000000000 : ℝ)=(100047785737845527873/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17292716744624677/50000000000000000000 : ℝ) ≤ ((1493508325342958621/1494000000000000000 : ℝ)+2*(522987064571/298800000000000 : ℝ)*(7117/50000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (1493508325342958621/1494000000000000000 : ℝ)+2*(522987064571/298800000000000 : ℝ)*(7117/50000 : ℝ)=(625105733404731/625000000000000 : ℝ) by norm_num, show 1+2*(17292716744624677/50000000000000000000 : ℝ)=(25017292716744624677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1493508325342958621/1494000000000000000 : ℝ)*(X 1 0+X 2 0)+(522987064571/298800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1493508325342958621/1494000000000000000 : ℝ)) (alpha := (522987064571/298800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1493508325342958621/1494000000000000000 : ℝ)*(X 0 1+X 2 1)+(522987064571/298800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1493508325342958621/1494000000000000000 : ℝ)) (alpha := (522987064571/298800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1493508325342958621/1494000000000000000 : ℝ)*(X 0 2+X 1 2)+(522987064571/298800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1493508325342958621/1494000000000000000 : ℝ)) (alpha := (522987064571/298800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-268588459/1250000000 : ℝ)*X 0 0+(5393931717/10000000000 : ℝ)*X 0 1+(5264834659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345006883/10000000000 : ℝ)*X 1 0+(-276775109/1250000000 : ℝ)*X 1 1+(263241733/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672503441/5000000000 : ℝ)*X 2 0+(2632417331/5000000000 : ℝ)*X 2 1+(-2214200871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((87185359/200000000 : ℝ)*X 0 0+(423178589/1000000000 : ℝ)*X 0 1+(4490536851/10000000000 : ℝ)*X 0 2+(87185359/200000000 : ℝ)*X 1 0+(423178589/1000000000 : ℝ)*X 1 1+(4490536851/10000000000 : ℝ)*X 1 2+(87185359/200000000 : ℝ)*X 2 0+(423178589/1000000000 : ℝ)*X 2 1+(4490536851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-134294551/625000000 : ℝ)*X 0 0+(1053033491/2000000000 : ℝ)*X 0 1+(21068741/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312209539/10000000000 : ℝ)*X 1 0+(-2085437587/10000000000 : ℝ)*X 1 1+(134839941/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312209163/10000000000 : ℝ)*X 2 0+(1348399493/2500000000 : ℝ)*X 2 1+(-521359411/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359278271/10000000000 : ℝ)*X 0 0+(280616867/625000000 : ℝ)*X 0 1+(1058113839/2500000000 : ℝ)*X 0 2+(4359278271/10000000000 : ℝ)*X 1 0+(280616867/625000000 : ℝ)*X 1 1+(1058113839/2500000000 : ℝ)*X 1 2+(4359278271/10000000000 : ℝ)*X 2 0+(280616867/625000000 : ℝ)*X 2 1+(1058113839/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40983007316366379124123/8300000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9775759/1000000000000 : ℝ)*(base19) + (454305693/50000000000000 : ℝ)*(base23) + (18043481/50000000000000 : ℝ)*(lower2) + (124909807/100000000000000 : ℝ)*(upper3) + (19117823/25000000000000 : ℝ)*(upper5) + (5805455314989/100000000000 : ℝ)*(major0) + (5805455314989/100000000000 : ℝ)*(major1) + (5805455314989/100000000000 : ℝ)*(major2) + (7746137423171767/100000000000000 : ℝ)*(sp0) + (2420675860823/31250000000 : ℝ)*(sp1) + (3873081411799057/50000000000000 : ℝ)*(sp2) + (241545790454133/6250000000000 : ℝ)*(sp3) + (6577259433/25000000000000 : ℝ)*(sp4) + (7042955987/50000000000000 : ℝ)*(sp7) + (1932373366589051/50000000000000 : ℝ)*(f.failure) + (15492327464419/200000000000 : ℝ)*(f.sum) + (228146672629/31125000000000000000000000 : ℝ)*base66 + (106826149892959/16600000000000000000000000000 : ℝ)*base68 + (117718292697041/16600000000000000000000000000 : ℝ)*base69 + (2004178730841/16600000000000000000000000000 : ℝ)*base71 + (340663225651/124500000000000000000000000 : ℝ)*base74 + (197290579347959/16600000000000000000000000000 : ℝ)*base76 + (316535740285959/16600000000000000000000000000 : ℝ)*base78 + (81783082278359/16600000000000000000000000000 : ℝ)*base80 + (38004463/972656250000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10396323/5000000000000000000000 : ℝ)*base89 + (10396323/5000000000000000000000 : ℝ)*base91 + (10396323/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18485380986375983729791337/8300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202262193/20000000000000 : ℝ)*(base19) + (466469231/100000000000000 : ℝ)*(base23) + (47157169/100000000000000 : ℝ)*(upper3) + (20875801/100000000000000 : ℝ)*(lower4) + (3696773/12500000000000 : ℝ)*(upper5) + (5835551462070409/100000000000000 : ℝ)*(major0) + (5835551462070409/100000000000000 : ℝ)*(major1) + (5835551462070409/100000000000000 : ℝ)*(major2) + (5826052749/20000000000000 : ℝ)*(sp1) + (11890770189/50000000000000 : ℝ)*(sp2) + (7786320825811941/100000000000000 : ℝ)*(sp4) + (7786290684237231/100000000000000 : ℝ)*(sp5) + (1946574144450583/25000000000000 : ℝ)*(sp6) + (776956404818079/20000000000000 : ℝ)*(sp7) + (776956404818079/20000000000000 : ℝ)*(f.failure) + (7786320825811941/100000000000000 : ℝ)*(f.sum) + (66561309815879/14940000000000000000000000000 : ℝ)*base65 + (148548419964471221/16600000000000000000000000000000 : ℝ)*base67 + (81987963788128779/16600000000000000000000000000000 : ℝ)*base70 + (157068356784071221/16600000000000000000000000000000 : ℝ)*base71 + (55160281866719/14940000000000000000000000000 : ℝ)*base73 + (56916709385471221/16600000000000000000000000000000 : ℝ)*base75 + (2081690395271221/16600000000000000000000000000000 : ℝ)*base77 + (21360428266528779/16600000000000000000000000000000 : ℝ)*base80 + (59359043803979/14940000000000000000000000000 : ℝ)*base81 + (447833/2000000000000000000000 : ℝ)*base90 + (447833/2000000000000000000000 : ℝ)*base92 + (447833/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1180_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1180_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1180_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2049/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1180_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1180_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1180_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2049/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1180_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
