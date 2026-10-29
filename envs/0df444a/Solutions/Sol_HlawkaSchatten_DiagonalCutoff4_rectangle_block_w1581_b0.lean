-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1581_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:30:01.225532+00:00
-- url     : https://prove2.me/submissions/4537c5d0-c9f6-4233-b7c5-2e6d8aaa7e62

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
theorem support_rectangle_w1581_s0_0 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1615033203/10000000000 : ℝ)*x 0 + (5861641459/10000000000 : ℝ)*x 1 + (4883736787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1615033203/10000000000 : ℝ)^4659 ≤ (9663216408283/100000000000000 : ℝ)^3635 := by
    have hnat : (1615033203 : ℕ)^4659*100000000000000^3635 ≤ 9663216408283^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615033203 10000000000 9663216408283 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5861641459/10000000000 : ℝ)^4659 ≤ (25213838637993/50000000000000 : ℝ)^3635 := by
    have hnat : (5861641459 : ℕ)^4659*50000000000000^3635 ≤ 25213838637993^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5861641459 10000000000 25213838637993 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4883736787/10000000000 : ℝ)^4659 ≤ (7981821259491/20000000000000 : ℝ)^3635 := by
    have hnat : (4883736787 : ℕ)^4659*20000000000000^3635 ≤ 7981821259491^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4883736787 10000000000 7981821259491 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1615033203/10000000000 : ℝ), (5861641459/10000000000 : ℝ), (4883736787/10000000000 : ℝ)] ![(9663216408283/100000000000000 : ℝ), (25213838637993/50000000000000 : ℝ), (7981821259491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1615033203/10000000000 : ℝ)|^4659 ≤ (9663216408283/100000000000000 : ℝ)^3635
        have hw : |(-1615033203/10000000000 : ℝ)|=(1615033203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5861641459/10000000000 : ℝ)|^4659 ≤ (25213838637993/50000000000000 : ℝ)^3635
        have hw : |(5861641459/10000000000 : ℝ)|=(5861641459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4883736787/10000000000 : ℝ)|^4659 ≤ (7981821259491/20000000000000 : ℝ)^3635
        have hw : |(4883736787/10000000000 : ℝ)|=(4883736787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s0_1 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2731568441/5000000000 : ℝ)*x 0 + (-431700117/2000000000 : ℝ)*x 1 + (2441868373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2731568441/5000000000 : ℝ)^4659 ≤ (46076346541783/100000000000000 : ℝ)^3635 := by
    have hnat : (2731568441 : ℕ)^4659*100000000000000^3635 ≤ 46076346541783^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731568441 5000000000 46076346541783 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431700117/2000000000 : ℝ)^4659 ≤ (2802909514067/20000000000000 : ℝ)^3635 := by
    have hnat : (431700117 : ℕ)^4659*20000000000000^3635 ≤ 2802909514067^3635*2000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431700117 2000000000 2802909514067 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2441868373/5000000000 : ℝ)^4659 ≤ (1596364234721/4000000000000 : ℝ)^3635 := by
    have hnat : (2441868373 : ℕ)^4659*4000000000000^3635 ≤ 1596364234721^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441868373 5000000000 1596364234721 4000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2731568441/5000000000 : ℝ), (-431700117/2000000000 : ℝ), (2441868373/5000000000 : ℝ)] ![(46076346541783/100000000000000 : ℝ), (2802909514067/20000000000000 : ℝ), (1596364234721/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2731568441/5000000000 : ℝ)|^4659 ≤ (46076346541783/100000000000000 : ℝ)^3635
        have hw : |(2731568441/5000000000 : ℝ)|=(2731568441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-431700117/2000000000 : ℝ)|^4659 ≤ (2802909514067/20000000000000 : ℝ)^3635
        have hw : |(-431700117/2000000000 : ℝ)|=(431700117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2441868373/5000000000 : ℝ)|^4659 ≤ (1596364234721/4000000000000 : ℝ)^3635
        have hw : |(2441868373/5000000000 : ℝ)|=(2441868373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s0_2 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5463136951/10000000000 : ℝ)*x 0 + (4883736651/10000000000 : ℝ)*x 1 + (-2158500617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5463136951/10000000000 : ℝ)^4659 ≤ (46076347287671/100000000000000 : ℝ)^3635 := by
    have hnat : (5463136951 : ℕ)^4659*100000000000000^3635 ≤ 46076347287671^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463136951 10000000000 46076347287671 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4883736651/10000000000 : ℝ)^4659 ≤ (19954552436503/50000000000000 : ℝ)^3635 := by
    have hnat : (4883736651 : ℕ)^4659*50000000000000^3635 ≤ 19954552436503^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4883736651 10000000000 19954552436503 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158500617/10000000000 : ℝ)^4659 ≤ (1751818479579/12500000000000 : ℝ)^3635 := by
    have hnat : (2158500617 : ℕ)^4659*12500000000000^3635 ≤ 1751818479579^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158500617 10000000000 1751818479579 12500000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5463136951/10000000000 : ℝ), (4883736651/10000000000 : ℝ), (-2158500617/10000000000 : ℝ)] ![(46076347287671/100000000000000 : ℝ), (19954552436503/50000000000000 : ℝ), (1751818479579/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5463136951/10000000000 : ℝ)|^4659 ≤ (46076347287671/100000000000000 : ℝ)^3635
        have hw : |(5463136951/10000000000 : ℝ)|=(5463136951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4883736651/10000000000 : ℝ)|^4659 ≤ (19954552436503/50000000000000 : ℝ)^3635
        have hw : |(4883736651/10000000000 : ℝ)|=(4883736651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2158500617/10000000000 : ℝ)|^4659 ≤ (1751818479579/12500000000000 : ℝ)^3635
        have hw : |(-2158500617/10000000000 : ℝ)|=(2158500617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s0_3 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (825404679/2000000000 : ℝ)*x 0 + (3093817989/10000000000 : ℝ)*x 1 + (5419530897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825404679/2000000000 : ℝ)^4659 ≤ (32163232231679/100000000000000 : ℝ)^3635 := by
    have hnat : (825404679 : ℕ)^4659*100000000000000^3635 ≤ 32163232231679^3635*2000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825404679 2000000000 32163232231679 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3093817989/10000000000 : ℝ)^4659 ≤ (1389454335553/6250000000000 : ℝ)^3635 := by
    have hnat : (3093817989 : ℕ)^4659*6250000000000^3635 ≤ 1389454335553^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093817989 10000000000 1389454335553 6250000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419530897/10000000000 : ℝ)^4659 ≤ (5700687298077/12500000000000 : ℝ)^3635 := by
    have hnat : (5419530897 : ℕ)^4659*12500000000000^3635 ≤ 5700687298077^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419530897 10000000000 5700687298077 12500000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(825404679/2000000000 : ℝ), (3093817989/10000000000 : ℝ), (5419530897/10000000000 : ℝ)] ![(32163232231679/100000000000000 : ℝ), (1389454335553/6250000000000 : ℝ), (5700687298077/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(825404679/2000000000 : ℝ)|^4659 ≤ (32163232231679/100000000000000 : ℝ)^3635
        have hw : |(825404679/2000000000 : ℝ)|=(825404679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3093817989/10000000000 : ℝ)|^4659 ≤ (1389454335553/6250000000000 : ℝ)^3635
        have hw : |(3093817989/10000000000 : ℝ)|=(3093817989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419530897/10000000000 : ℝ)|^4659 ≤ (5700687298077/12500000000000 : ℝ)^3635
        have hw : |(5419530897/10000000000 : ℝ)|=(5419530897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s0_4 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1618007517/10000000000 : ℝ)*x 0 + (4908318773/10000000000 : ℝ)*x 1 + (1459047549/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1618007517/10000000000 : ℝ)^4659 ≤ (9686031801229/100000000000000 : ℝ)^3635 := by
    have hnat : (1618007517 : ℕ)^4659*100000000000000^3635 ≤ 9686031801229^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1618007517 10000000000 9686031801229 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4908318773/10000000000 : ℝ)^4659 ≤ (10041689414467/25000000000000 : ℝ)^3635 := by
    have hnat : (4908318773 : ℕ)^4659*25000000000000^3635 ≤ 10041689414467^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4908318773 10000000000 10041689414467 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1459047549/2500000000 : ℝ)^4659 ≤ (1567100328913/3125000000000 : ℝ)^3635 := by
    have hnat : (1459047549 : ℕ)^4659*3125000000000^3635 ≤ 1567100328913^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459047549 2500000000 1567100328913 3125000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1618007517/10000000000 : ℝ), (4908318773/10000000000 : ℝ), (1459047549/2500000000 : ℝ)] ![(9686031801229/100000000000000 : ℝ), (10041689414467/25000000000000 : ℝ), (1567100328913/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1618007517/10000000000 : ℝ)|^4659 ≤ (9686031801229/100000000000000 : ℝ)^3635
        have hw : |(-1618007517/10000000000 : ℝ)|=(1618007517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4908318773/10000000000 : ℝ)|^4659 ≤ (10041689414467/25000000000000 : ℝ)^3635
        have hw : |(4908318773/10000000000 : ℝ)|=(4908318773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1459047549/2500000000 : ℝ)|^4659 ≤ (1567100328913/3125000000000 : ℝ)^3635
        have hw : |(1459047549/2500000000 : ℝ)|=(1459047549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s0_5 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324736879/625000000 : ℝ)*x 0 + (-120604739/1000000000 : ℝ)*x 1 + (2918095087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324736879/625000000 : ℝ)^4659 ≤ (10801623971869/25000000000000 : ℝ)^3635 := by
    have hnat : (324736879 : ℕ)^4659*25000000000000^3635 ≤ 10801623971869^3635*625000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324736879 625000000 10801623971869 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120604739/1000000000 : ℝ)^4659 ≤ (830786726773/12500000000000 : ℝ)^3635 := by
    have hnat : (120604739 : ℕ)^4659*12500000000000^3635 ≤ 830786726773^3635*1000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120604739 1000000000 830786726773 12500000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2918095087/5000000000 : ℝ)^4659 ≤ (5014721028293/10000000000000 : ℝ)^3635 := by
    have hnat : (2918095087 : ℕ)^4659*10000000000000^3635 ≤ 5014721028293^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2918095087 5000000000 5014721028293 10000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324736879/625000000 : ℝ), (-120604739/1000000000 : ℝ), (2918095087/5000000000 : ℝ)] ![(10801623971869/25000000000000 : ℝ), (830786726773/12500000000000 : ℝ), (5014721028293/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324736879/625000000 : ℝ)|^4659 ≤ (10801623971869/25000000000000 : ℝ)^3635
        have hw : |(324736879/625000000 : ℝ)|=(324736879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120604739/1000000000 : ℝ)|^4659 ≤ (830786726773/12500000000000 : ℝ)^3635
        have hw : |(-120604739/1000000000 : ℝ)|=(120604739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2918095087/5000000000 : ℝ)|^4659 ≤ (5014721028293/10000000000000 : ℝ)^3635
        have hw : |(2918095087/5000000000 : ℝ)|=(2918095087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s0_6 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324736783/625000000 : ℝ)*x 0 + (1459047947/2500000000 : ℝ)*x 1 + (-150755899/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324736783/625000000 : ℝ)^4659 ≤ (4320647951641/10000000000000 : ℝ)^3635 := by
    have hnat : (324736783 : ℕ)^4659*10000000000000^3635 ≤ 4320647951641^3635*625000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324736783 625000000 4320647951641 10000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1459047947/2500000000 : ℝ)^4659 ≤ (50147228057913/100000000000000 : ℝ)^3635 := by
    have hnat : (1459047947 : ℕ)^4659*100000000000000^3635 ≤ 50147228057913^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459047947 2500000000 50147228057913 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150755899/1250000000 : ℝ)^4659 ≤ (1329258483133/20000000000000 : ℝ)^3635 := by
    have hnat : (150755899 : ℕ)^4659*20000000000000^3635 ≤ 1329258483133^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150755899 1250000000 1329258483133 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324736783/625000000 : ℝ), (1459047947/2500000000 : ℝ), (-150755899/1250000000 : ℝ)] ![(4320647951641/10000000000000 : ℝ), (50147228057913/100000000000000 : ℝ), (1329258483133/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324736783/625000000 : ℝ)|^4659 ≤ (4320647951641/10000000000000 : ℝ)^3635
        have hw : |(324736783/625000000 : ℝ)|=(324736783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1459047947/2500000000 : ℝ)|^4659 ≤ (50147228057913/100000000000000 : ℝ)^3635
        have hw : |(1459047947/2500000000 : ℝ)|=(1459047947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-150755899/1250000000 : ℝ)|^4659 ≤ (1329258483133/20000000000000 : ℝ)^3635
        have hw : |(-150755899/1250000000 : ℝ)|=(150755899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s0_7 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4134094299/10000000000 : ℝ)*x 0 + (2680531913/5000000000 : ℝ)*x 1 + (3154346519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4134094299/10000000000 : ℝ)^4659 ≤ (32233878746657/100000000000000 : ℝ)^3635 := by
    have hnat : (4134094299 : ℕ)^4659*100000000000000^3635 ≤ 32233878746657^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134094299 10000000000 32233878746657 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2680531913/5000000000 : ℝ)^4659 ≤ (22487928697401/50000000000000 : ℝ)^3635 := by
    have hnat : (2680531913 : ℕ)^4659*50000000000000^3635 ≤ 22487928697401^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680531913 5000000000 22487928697401 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154346519/10000000000 : ℝ)^4659 ≤ (4558052768619/20000000000000 : ℝ)^3635 := by
    have hnat : (3154346519 : ℕ)^4659*20000000000000^3635 ≤ 4558052768619^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154346519 10000000000 4558052768619 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4134094299/10000000000 : ℝ), (2680531913/5000000000 : ℝ), (3154346519/10000000000 : ℝ)] ![(32233878746657/100000000000000 : ℝ), (22487928697401/50000000000000 : ℝ), (4558052768619/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4134094299/10000000000 : ℝ)|^4659 ≤ (32233878746657/100000000000000 : ℝ)^3635
        have hw : |(4134094299/10000000000 : ℝ)|=(4134094299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2680531913/5000000000 : ℝ)|^4659 ≤ (22487928697401/50000000000000 : ℝ)^3635
        have hw : |(2680531913/5000000000 : ℝ)|=(2680531913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154346519/10000000000 : ℝ)|^4659 ≤ (4558052768619/20000000000000 : ℝ)^3635
        have hw : |(3154346519/10000000000 : ℝ)|=(3154346519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1581_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1837/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24621/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4657/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4657 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4657*1^1024 ≤ 0^1024*1^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4657/1024 : ℝ) ≤ (193703702847070057/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4657 ≤ (193703702847070057/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4657*12500000000000000000^1024 ≤ 193703702847070057^1024*5^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 193703702847070057 12500000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (193703702847070057/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4657 := by
      have hnat : (1 : ℕ)^1024*1^4657 ≤ 1^4657*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12693703702847070057/12500000000000000000 : ℝ) ≤ (10033869798671549/10000000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (12693703702847070057/12500000000000000000 : ℝ)^1024 ≤ (10033869798671549/10000000000000000 : ℝ)^4657 := by
      have hnat : (12693703702847070057 : ℕ)^1024*10000000000000000^4657 ≤ 10033869798671549^4657*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12693703702847070057 12500000000000000000 10033869798671549 10000000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10033869798671549/10000000000000000 : ℝ)) (X := (12693703702847070057/12500000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6443703702847070057/6250000000000000000 : ℝ) ≤ (5033869798671549/5000000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (6443703702847070057/6250000000000000000 : ℝ)^1024 ≤ (5033869798671549/5000000000000000 : ℝ)^4657 := by
      have hnat : (6443703702847070057 : ℕ)^1024*5000000000000000^4657 ≤ 5033869798671549^4657*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6443703702847070057 6250000000000000000 5033869798671549 5000000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5033869798671549/5000000000000000 : ℝ)) (X := (6443703702847070057/6250000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(33869798671549/4000000000000000 : ℝ)*(0 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(33869798671549/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(193703702847070057/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(33869798671549/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4657/1024 : ℝ) := by
    rw [show (1 : ℝ)+(33869798671549/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10033869798671549/10000000000000000 : ℝ) by norm_num, show 1+(193703702847070057/12500000000000000000 : ℝ)+(0 : ℝ)=(12693703702847070057/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(193703702847070057/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(33869798671549/4000000000000000 : ℝ)*(2/5 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(33869798671549/4000000000000000 : ℝ)*(2/5 : ℝ)=(5033869798671549/5000000000000000 : ℝ) by norm_num, show 1+2*(193703702847070057/12500000000000000000 : ℝ)=(6443703702847070057/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(33869798671549/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (33869798671549/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(33869798671549/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (33869798671549/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(33869798671549/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (33869798671549/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1615033203/10000000000 : ℝ)*X 0 0+(5861641459/10000000000 : ℝ)*X 0 1+(4883736787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2731568441/5000000000 : ℝ)*X 1 0+(-431700117/2000000000 : ℝ)*X 1 1+(2441868373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5463136951/10000000000 : ℝ)*X 2 0+(4883736651/10000000000 : ℝ)*X 2 1+(-2158500617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((825404679/2000000000 : ℝ)*X 0 0+(3093817989/10000000000 : ℝ)*X 0 1+(5419530897/10000000000 : ℝ)*X 0 2+(825404679/2000000000 : ℝ)*X 1 0+(3093817989/10000000000 : ℝ)*X 1 1+(5419530897/10000000000 : ℝ)*X 1 2+(825404679/2000000000 : ℝ)*X 2 0+(3093817989/10000000000 : ℝ)*X 2 1+(5419530897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1618007517/10000000000 : ℝ)*X 0 0+(4908318773/10000000000 : ℝ)*X 0 1+(1459047549/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324736879/625000000 : ℝ)*X 1 0+(-120604739/1000000000 : ℝ)*X 1 1+(2918095087/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((324736783/625000000 : ℝ)*X 2 0+(1459047947/2500000000 : ℝ)*X 2 1+(-150755899/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4134094299/10000000000 : ℝ)*X 0 0+(2680531913/5000000000 : ℝ)*X 0 1+(3154346519/10000000000 : ℝ)*X 0 2+(4134094299/10000000000 : ℝ)*X 1 0+(2680531913/5000000000 : ℝ)*X 1 1+(3154346519/10000000000 : ℝ)*X 1 2+(4134094299/10000000000 : ℝ)*X 2 0+(2680531913/5000000000 : ℝ)*X 2 1+(3154346519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (393288478301869728170943/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (566073/1562500000000 : ℝ)*(base1) + (368739103/50000000000000 : ℝ)*(base19) + (375196871/50000000000000 : ℝ)*(base23) + (95929181/100000000000000 : ℝ)*(upper3) + (17988749/20000000000000 : ℝ)*(upper5) + (363144498358323/50000000000000 : ℝ)*(major0) + (363144498358323/50000000000000 : ℝ)*(major1) + (363144498358323/50000000000000 : ℝ)*(major2) + (12782464710367/1250000000000 : ℝ)*(sp0) + (15978111369489/1562500000000 : ℝ)*(sp1) + (1022599114731761/100000000000000 : ℝ)*(sp2) + (107494195204077/25000000000000 : ℝ)*(sp3) + (544904963/20000000000000 : ℝ)*(sp4) + (1180166643/100000000000000 : ℝ)*(sp7) + (429977997211623/100000000000000 : ℝ)*(f.failure) + (511299932562751/50000000000000 : ℝ)*(f.sum) + (85795160747673/100000000000000000000000000000 : ℝ)*base66 + (2133125005547673/200000000000000000000000000000 : ℝ)*base68 + (1701606023147673/200000000000000000000000000000 : ℝ)*base70 + (878636210347673/200000000000000000000000000000 : ℝ)*base72 + (358088469547673/100000000000000000000000000000 : ℝ)*base74 + (200922225652327/200000000000000000000000000000 : ℝ)*base75 + (1540082138147673/200000000000000000000000000000 : ℝ)*base78 + (1636361840747673/200000000000000000000000000000 : ℝ)*base80 + (19713041852327/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (105708003/10000000000000000000000 : ℝ)*base89 + (105708003/10000000000000000000000 : ℝ)*base91 + (105708003/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (619907564906690336235297/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (222262601/12500000000000 : ℝ)*(base19) + (1919704897/100000000000000 : ℝ)*(base23) + (274529917/50000000000000 : ℝ)*(base39) + (2457877/1250000000000 : ℝ)*(upper3) + (321363531/50000000000000 : ℝ)*(upper5) + (382723473401049/50000000000000 : ℝ)*(major0) + (382723473401049/50000000000000 : ℝ)*(major1) + (153089279548453/20000000000000 : ℝ)*(major2) + (5683912441/100000000000000 : ℝ)*(sp1) + (4130969893/100000000000000 : ℝ)*(sp2) + (1077732830309733/100000000000000 : ℝ)*(sp4) + (269431342074121/25000000000000 : ℝ)*(sp5) + (134715916086847/12500000000000 : ℝ)*(sp6) + (45316030759877/10000000000000 : ℝ)*(sp7) + (45316030759877/10000000000000 : ℝ)*(f.failure) + (538866689684783/50000000000000 : ℝ)*(f.sum) + (669824388828287/400000000000000000000000000000 : ℝ)*base65 + (185694952256303/80000000000000000000000000000 : ℝ)*base68 + (113225243454901/200000000000000000000000000000 : ℝ)*base69 + (140725715376303/80000000000000000000000000000 : ℝ)*base72 + (1268508386428287/400000000000000000000000000000 : ℝ)*base73 + (850740263345099/200000000000000000000000000000 : ℝ)*base76 + (473054537145099/200000000000000000000000000000 : ℝ)*base78 + (99631267145099/200000000000000000000000000000 : ℝ)*base80 + (375518237354901/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (53497/1000000000000000000000 : ℝ)*base89 + (53497/1000000000000000000000 : ℝ)*base91 + (9946503/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1581_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1837/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24621/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1581_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1581_s1_0 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1750877513/10000000000 : ℝ)*x 0 + (5528684297/10000000000 : ℝ)*x 1 + (5129083439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1750877513/10000000000 : ℝ)^4659 ≤ (535854214239/5000000000000 : ℝ)^3635 := by
    have hnat : (1750877513 : ℕ)^4659*5000000000000^3635 ≤ 535854214239^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750877513 10000000000 535854214239 5000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528684297/10000000000 : ℝ)^4659 ≤ (584826322153/1250000000000 : ℝ)^3635 := by
    have hnat : (5528684297 : ℕ)^4659*1250000000000^3635 ≤ 584826322153^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528684297 10000000000 584826322153 1250000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129083439/10000000000 : ℝ)^4659 ≤ (10624202481637/25000000000000 : ℝ)^3635 := by
    have hnat : (5129083439 : ℕ)^4659*25000000000000^3635 ≤ 10624202481637^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129083439 10000000000 10624202481637 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1750877513/10000000000 : ℝ), (5528684297/10000000000 : ℝ), (5129083439/10000000000 : ℝ)] ![(535854214239/5000000000000 : ℝ), (584826322153/1250000000000 : ℝ), (10624202481637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1750877513/10000000000 : ℝ)|^4659 ≤ (535854214239/5000000000000 : ℝ)^3635
        have hw : |(-1750877513/10000000000 : ℝ)|=(1750877513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528684297/10000000000 : ℝ)|^4659 ≤ (584826322153/1250000000000 : ℝ)^3635
        have hw : |(5528684297/10000000000 : ℝ)|=(5528684297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129083439/10000000000 : ℝ)|^4659 ≤ (10624202481637/25000000000000 : ℝ)^3635
        have hw : |(5129083439/10000000000 : ℝ)|=(5129083439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s1_1 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687297233/5000000000 : ℝ)*x 0 + (-1959658357/10000000000 : ℝ)*x 1 + (205163323/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687297233/5000000000 : ℝ)^4659 ≤ (45121399742699/100000000000000 : ℝ)^3635 := by
    have hnat : (2687297233 : ℕ)^4659*100000000000000^3635 ≤ 45121399742699^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687297233 5000000000 45121399742699 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1959658357/10000000000 : ℝ)^4659 ≤ (6190897090553/50000000000000 : ℝ)^3635 := by
    have hnat : (1959658357 : ℕ)^4659*50000000000000^3635 ≤ 6190897090553^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959658357 10000000000 6190897090553 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205163323/400000000 : ℝ)^4659 ≤ (42496806061043/100000000000000 : ℝ)^3635 := by
    have hnat : (205163323 : ℕ)^4659*100000000000000^3635 ≤ 42496806061043^3635*400000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205163323 400000000 42496806061043 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687297233/5000000000 : ℝ), (-1959658357/10000000000 : ℝ), (205163323/400000000 : ℝ)] ![(45121399742699/100000000000000 : ℝ), (6190897090553/50000000000000 : ℝ), (42496806061043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687297233/5000000000 : ℝ)|^4659 ≤ (45121399742699/100000000000000 : ℝ)^3635
        have hw : |(2687297233/5000000000 : ℝ)|=(2687297233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1959658357/10000000000 : ℝ)|^4659 ≤ (6190897090553/50000000000000 : ℝ)^3635
        have hw : |(-1959658357/10000000000 : ℝ)|=(1959658357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205163323/400000000 : ℝ)|^4659 ≤ (42496806061043/100000000000000 : ℝ)^3635
        have hw : |(205163323/400000000 : ℝ)|=(205163323/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s1_2 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671824271/1250000000 : ℝ)*x 0 + (5129083351/10000000000 : ℝ)*x 1 + (-1959658391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671824271/1250000000 : ℝ)^4659 ≤ (11280349134031/25000000000000 : ℝ)^3635 := by
    have hnat : (671824271 : ℕ)^4659*25000000000000^3635 ≤ 11280349134031^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671824271 1250000000 11280349134031 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129083351/10000000000 : ℝ)^4659 ≤ (4249680899203/10000000000000 : ℝ)^3635 := by
    have hnat : (5129083351 : ℕ)^4659*10000000000000^3635 ≤ 4249680899203^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129083351 10000000000 4249680899203 10000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1959658391/10000000000 : ℝ)^4659 ≤ (12381794456447/100000000000000 : ℝ)^3635 := by
    have hnat : (1959658391 : ℕ)^4659*100000000000000^3635 ≤ 12381794456447^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959658391 10000000000 12381794456447 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671824271/1250000000 : ℝ), (5129083351/10000000000 : ℝ), (-1959658391/10000000000 : ℝ)] ![(11280349134031/25000000000000 : ℝ), (4249680899203/10000000000000 : ℝ), (12381794456447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671824271/1250000000 : ℝ)|^4659 ≤ (11280349134031/25000000000000 : ℝ)^3635
        have hw : |(671824271/1250000000 : ℝ)|=(671824271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129083351/10000000000 : ℝ)|^4659 ≤ (4249680899203/10000000000000 : ℝ)^3635
        have hw : |(5129083351/10000000000 : ℝ)|=(5129083351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1959658391/10000000000 : ℝ)|^4659 ≤ (12381794456447/100000000000000 : ℝ)^3635
        have hw : |(-1959658391/10000000000 : ℝ)|=(1959658391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s1_3 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6600717/15625000 : ℝ)*x 0 + (942660131/2500000000 : ℝ)*x 1 + (4720996619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6600717/15625000 : ℝ)^4659 ≤ (33139709100609/100000000000000 : ℝ)^3635 := by
    have hnat : (6600717 : ℕ)^4659*100000000000000^3635 ≤ 33139709100609^3635*15625000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6600717 15625000 33139709100609 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (942660131/2500000000 : ℝ)^4659 ≤ (28647642220307/100000000000000 : ℝ)^3635 := by
    have hnat : (942660131 : ℕ)^4659*100000000000000^3635 ≤ 28647642220307^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942660131 2500000000 28647642220307 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4720996619/10000000000 : ℝ)^4659 ≤ (38212648668697/100000000000000 : ℝ)^3635 := by
    have hnat : (4720996619 : ℕ)^4659*100000000000000^3635 ≤ 38212648668697^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4720996619 10000000000 38212648668697 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6600717/15625000 : ℝ), (942660131/2500000000 : ℝ), (4720996619/10000000000 : ℝ)] ![(33139709100609/100000000000000 : ℝ), (28647642220307/100000000000000 : ℝ), (38212648668697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6600717/15625000 : ℝ)|^4659 ≤ (33139709100609/100000000000000 : ℝ)^3635
        have hw : |(6600717/15625000 : ℝ)|=(6600717/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(942660131/2500000000 : ℝ)|^4659 ≤ (28647642220307/100000000000000 : ℝ)^3635
        have hw : |(942660131/2500000000 : ℝ)|=(942660131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4720996619/10000000000 : ℝ)|^4659 ≤ (38212648668697/100000000000000 : ℝ)^3635
        have hw : |(4720996619/10000000000 : ℝ)|=(4720996619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s1_4 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-43776881/250000000 : ℝ)*x 0 + (5133144819/10000000000 : ℝ)*x 1 + (2762281977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43776881/250000000 : ℝ)^4659 ≤ (5359317767867/50000000000000 : ℝ)^3635 := by
    have hnat : (43776881 : ℕ)^4659*50000000000000^3635 ≤ 5359317767867^3635*250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43776881 250000000 5359317767867 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133144819/10000000000 : ℝ)^4659 ≤ (42539944639593/100000000000000 : ℝ)^3635 := by
    have hnat : (5133144819 : ℕ)^4659*100000000000000^3635 ≤ 42539944639593^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133144819 10000000000 42539944639593 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2762281977/5000000000 : ℝ)^4659 ≤ (11685354950981/25000000000000 : ℝ)^3635 := by
    have hnat : (2762281977 : ℕ)^4659*25000000000000^3635 ≤ 11685354950981^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762281977 5000000000 11685354950981 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43776881/250000000 : ℝ), (5133144819/10000000000 : ℝ), (2762281977/5000000000 : ℝ)] ![(5359317767867/50000000000000 : ℝ), (42539944639593/100000000000000 : ℝ), (11685354950981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43776881/250000000 : ℝ)|^4659 ≤ (5359317767867/50000000000000 : ℝ)^3635
        have hw : |(-43776881/250000000 : ℝ)|=(43776881/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133144819/10000000000 : ℝ)|^4659 ≤ (42539944639593/100000000000000 : ℝ)^3635
        have hw : |(5133144819/10000000000 : ℝ)|=(5133144819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2762281977/5000000000 : ℝ)|^4659 ≤ (11685354950981/25000000000000 : ℝ)^3635
        have hw : |(2762281977/5000000000 : ℝ)|=(2762281977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s1_5 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317139903/2500000000 : ℝ)*x 0 + (-782088763/5000000000 : ℝ)*x 1 + (5524564621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317139903/2500000000 : ℝ)^4659 ≤ (21991808284531/50000000000000 : ℝ)^3635 := by
    have hnat : (1317139903 : ℕ)^4659*50000000000000^3635 ≤ 21991808284531^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317139903 2500000000 21991808284531 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782088763/5000000000 : ℝ)^4659 ≤ (9274956377803/100000000000000 : ℝ)^3635 := by
    have hnat : (782088763 : ℕ)^4659*100000000000000^3635 ≤ 9274956377803^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782088763 5000000000 9274956377803 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5524564621/10000000000 : ℝ)^4659 ≤ (11685356759229/25000000000000 : ℝ)^3635 := by
    have hnat : (5524564621 : ℕ)^4659*25000000000000^3635 ≤ 11685356759229^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524564621 10000000000 11685356759229 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317139903/2500000000 : ℝ), (-782088763/5000000000 : ℝ), (5524564621/10000000000 : ℝ)] ![(21991808284531/50000000000000 : ℝ), (9274956377803/100000000000000 : ℝ), (11685356759229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317139903/2500000000 : ℝ)|^4659 ≤ (21991808284531/50000000000000 : ℝ)^3635
        have hw : |(1317139903/2500000000 : ℝ)|=(1317139903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-782088763/5000000000 : ℝ)|^4659 ≤ (9274956377803/100000000000000 : ℝ)^3635
        have hw : |(-782088763/5000000000 : ℝ)|=(782088763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5524564621/10000000000 : ℝ)|^4659 ≤ (11685356759229/25000000000000 : ℝ)^3635
        have hw : |(5524564621/10000000000 : ℝ)|=(5524564621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s1_6 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268558799/10000000000 : ℝ)*x 0 + (5524564939/10000000000 : ℝ)*x 1 + (-1564178217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268558799/10000000000 : ℝ)^4659 ≤ (43983607869891/100000000000000 : ℝ)^3635 := by
    have hnat : (5268558799 : ℕ)^4659*100000000000000^3635 ≤ 43983607869891^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268558799 10000000000 43983607869891 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5524564939/10000000000 : ℝ)^4659 ≤ (4674143048533/10000000000000 : ℝ)^3635 := by
    have hnat : (5524564939 : ℕ)^4659*10000000000000^3635 ≤ 4674143048533^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524564939 10000000000 4674143048533 10000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1564178217/10000000000 : ℝ)^4659 ≤ (927496162941/10000000000000 : ℝ)^3635 := by
    have hnat : (1564178217 : ℕ)^4659*10000000000000^3635 ≤ 927496162941^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564178217 10000000000 927496162941 10000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268558799/10000000000 : ℝ), (5524564939/10000000000 : ℝ), (-1564178217/10000000000 : ℝ)] ![(43983607869891/100000000000000 : ℝ), (4674143048533/10000000000000 : ℝ), (927496162941/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268558799/10000000000 : ℝ)|^4659 ≤ (43983607869891/100000000000000 : ℝ)^3635
        have hw : |(5268558799/10000000000 : ℝ)|=(5268558799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5524564939/10000000000 : ℝ)|^4659 ≤ (4674143048533/10000000000000 : ℝ)^3635
        have hw : |(5524564939/10000000000 : ℝ)|=(5524564939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1564178217/10000000000 : ℝ)|^4659 ≤ (927496162941/10000000000000 : ℝ)^3635
        have hw : |(-1564178217/10000000000 : ℝ)|=(1564178217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s1_7 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2112464139/5000000000 : ℝ)*x 0 + (4711338389/10000000000 : ℝ)*x 1 + (3780438867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112464139/5000000000 : ℝ)^4659 ≤ (33144428795581/100000000000000 : ℝ)^3635 := by
    have hnat : (2112464139 : ℕ)^4659*100000000000000^3635 ≤ 33144428795581^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112464139 5000000000 33144428795581 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4711338389/10000000000 : ℝ)^4659 ≤ (38112479500781/100000000000000 : ℝ)^3635 := by
    have hnat : (4711338389 : ℕ)^4659*100000000000000^3635 ≤ 38112479500781^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4711338389 10000000000 38112479500781 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3780438867/10000000000 : ℝ)^4659 ≤ (5748618337961/20000000000000 : ℝ)^3635 := by
    have hnat : (3780438867 : ℕ)^4659*20000000000000^3635 ≤ 5748618337961^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3780438867 10000000000 5748618337961 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2112464139/5000000000 : ℝ), (4711338389/10000000000 : ℝ), (3780438867/10000000000 : ℝ)] ![(33144428795581/100000000000000 : ℝ), (38112479500781/100000000000000 : ℝ), (5748618337961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2112464139/5000000000 : ℝ)|^4659 ≤ (33144428795581/100000000000000 : ℝ)^3635
        have hw : |(2112464139/5000000000 : ℝ)|=(2112464139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4711338389/10000000000 : ℝ)|^4659 ≤ (38112479500781/100000000000000 : ℝ)^3635
        have hw : |(4711338389/10000000000 : ℝ)|=(4711338389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3780438867/10000000000 : ℝ)|^4659 ≤ (5748618337961/20000000000000 : ℝ)^3635
        have hw : |(3780438867/10000000000 : ℝ)|=(3780438867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1581_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1837/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9191/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2207/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1837/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1837/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1837/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1837/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1837/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1837/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1837/50000 : ℝ) ^ (4657/1024 : ℝ) ≤ (3727141348741/12500000000000000000 : ℝ) := by
    have hpowers : (1837/50000 : ℝ)^4657 ≤ (3727141348741/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1837 : ℕ)^4657*12500000000000000000^1024 ≤ 3727141348741^1024*50000^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1837 50000 3727141348741 12500000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1837/50000 : ℝ)) (X := (3727141348741/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24621/100000 : ℝ) ^ (4657/1024 : ℝ) ≤ (170509516432882437/100000000000000000000 : ℝ) := by
    have hpowers : (24621/100000 : ℝ)^4657 ≤ (170509516432882437/100000000000000000000 : ℝ)^1024 := by
      have hnat : (24621 : ℕ)^4657*100000000000000000000^1024 ≤ 170509516432882437^1024*100000^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24621 100000 170509516432882437 100000000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24621/100000 : ℝ)) (X := (170509516432882437/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250003727141348741/6250000000000000000 : ℝ) ≤ (2500000327815491/2500000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (6250003727141348741/6250000000000000000 : ℝ)^1024 ≤ (2500000327815491/2500000000000000 : ℝ)^4657 := by
      have hnat : (6250003727141348741 : ℕ)^1024*2500000000000000^4657 ≤ 2500000327815491^4657*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250003727141348741 6250000000000000000 2500000327815491 2500000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000327815491/2500000000000000 : ℝ)) (X := (6250003727141348741/6250000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20034107866712734473/20000000000000000000 : ℝ) ≤ (10003747395945753/10000000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (20034107866712734473/20000000000000000000 : ℝ)^1024 ≤ (10003747395945753/10000000000000000 : ℝ)^4657 := by
      have hnat : (20034107866712734473 : ℕ)^1024*10000000000000000^4657 ≤ 10003747395945753^4657*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20034107866712734473 20000000000000000000 10003747395945753 10000000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003747395945753/10000000000000000 : ℝ)) (X := (20034107866712734473/20000000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50170509516432882437/50000000000000000000 : ℝ) ≤ (5003746740314771/5000000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (50170509516432882437/50000000000000000000 : ℝ)^1024 ≤ (5003746740314771/5000000000000000 : ℝ)^4657 := by
      have hnat : (50170509516432882437 : ℕ)^1024*5000000000000000^4657 ≤ 5003746740314771^4657*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50170509516432882437 50000000000000000000 5003746740314771 5000000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003746740314771/5000000000000000 : ℝ)) (X := (50170509516432882437/50000000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3727141348741/12500000000000000000 : ℝ) ≤ ((3272539081824185599/3272968750000000000 : ℝ)+2*(3746084683789/2094700000000000 : ℝ)*(1837/50000 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (3272539081824185599/3272968750000000000 : ℝ)+2*(3746084683789/2094700000000000 : ℝ)*(1837/50000 : ℝ)=(2500000327815491/2500000000000000 : ℝ) by norm_num, show 1+2*(3727141348741/12500000000000000000 : ℝ)=(6250003727141348741/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(170509516432882437/100000000000000000000 : ℝ)+(3727141348741/12500000000000000000 : ℝ) ≤ ((3272539081824185599/3272968750000000000 : ℝ)+(3746084683789/2094700000000000 : ℝ)*((24621/100000 : ℝ)+(1837/50000 : ℝ)))^(4657/1024 : ℝ) := by
    rw [show (3272539081824185599/3272968750000000000 : ℝ)+(3746084683789/2094700000000000 : ℝ)*((24621/100000 : ℝ)+(1837/50000 : ℝ))=(10003747395945753/10000000000000000 : ℝ) by norm_num, show 1+(170509516432882437/100000000000000000000 : ℝ)+(3727141348741/12500000000000000000 : ℝ)=(20034107866712734473/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(170509516432882437/100000000000000000000 : ℝ) ≤ ((3272539081824185599/3272968750000000000 : ℝ)+2*(3746084683789/2094700000000000 : ℝ)*(24621/100000 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (3272539081824185599/3272968750000000000 : ℝ)+2*(3746084683789/2094700000000000 : ℝ)*(24621/100000 : ℝ)=(5003746740314771/5000000000000000 : ℝ) by norm_num, show 1+2*(170509516432882437/100000000000000000000 : ℝ)=(50170509516432882437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3272539081824185599/3272968750000000000 : ℝ)*(X 1 0+X 2 0)+(3746084683789/2094700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (1837/50000 : ℝ)) (hi := (24621/100000 : ℝ)) (c := (3272539081824185599/3272968750000000000 : ℝ)) (alpha := (3746084683789/2094700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3272539081824185599/3272968750000000000 : ℝ)*(X 0 1+X 2 1)+(3746084683789/2094700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (1837/50000 : ℝ)) (hi := (24621/100000 : ℝ)) (c := (3272539081824185599/3272968750000000000 : ℝ)) (alpha := (3746084683789/2094700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3272539081824185599/3272968750000000000 : ℝ)*(X 0 2+X 1 2)+(3746084683789/2094700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (1837/50000 : ℝ)) (hi := (24621/100000 : ℝ)) (c := (3272539081824185599/3272968750000000000 : ℝ)) (alpha := (3746084683789/2094700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1750877513/10000000000 : ℝ)*X 0 0+(5528684297/10000000000 : ℝ)*X 0 1+(5129083439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687297233/5000000000 : ℝ)*X 1 0+(-1959658357/10000000000 : ℝ)*X 1 1+(205163323/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671824271/1250000000 : ℝ)*X 2 0+(5129083351/10000000000 : ℝ)*X 2 1+(-1959658391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((6600717/15625000 : ℝ)*X 0 0+(942660131/2500000000 : ℝ)*X 0 1+(4720996619/10000000000 : ℝ)*X 0 2+(6600717/15625000 : ℝ)*X 1 0+(942660131/2500000000 : ℝ)*X 1 1+(4720996619/10000000000 : ℝ)*X 1 2+(6600717/15625000 : ℝ)*X 2 0+(942660131/2500000000 : ℝ)*X 2 1+(4720996619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-43776881/250000000 : ℝ)*X 0 0+(5133144819/10000000000 : ℝ)*X 0 1+(2762281977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1317139903/2500000000 : ℝ)*X 1 0+(-782088763/5000000000 : ℝ)*X 1 1+(5524564621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5268558799/10000000000 : ℝ)*X 2 0+(5524564939/10000000000 : ℝ)*X 2 1+(-1564178217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2112464139/5000000000 : ℝ)*X 0 0+(4711338389/10000000000 : ℝ)*X 0 1+(3780438867/10000000000 : ℝ)*X 0 2+(2112464139/5000000000 : ℝ)*X 1 0+(4711338389/10000000000 : ℝ)*X 1 1+(3780438867/10000000000 : ℝ)*X 1 2+(2112464139/5000000000 : ℝ)*X 2 0+(4711338389/10000000000 : ℝ)*X 2 1+(3780438867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (610918250181800108563807593/327296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (571384903/50000000000000 : ℝ)*(base19) + (181259533/20000000000000 : ℝ)*(base23) + (10105509/100000000000000 : ℝ)*(upper2) + (116786433/100000000000000 : ℝ)*(upper3) + (31312367/50000000000000 : ℝ)*(upper4) + (888690663098311/50000000000000 : ℝ)*(major0) + (888690663098311/50000000000000 : ℝ)*(major1) + (888690663098311/50000000000000 : ℝ)*(major2) + (500501507163201/20000000000000 : ℝ)*(sp0) + (625628802893881/25000000000000 : ℝ)*(sp1) + (1251257724023833/50000000000000 : ℝ)*(sp2) + (263060330650649/25000000000000 : ℝ)*(sp3) + (4409264663/50000000000000 : ℝ)*(sp4) + (4913226747/100000000000000 : ℝ)*(sp7) + (1052246235829343/100000000000000 : ℝ)*(f.failure) + (2502516354345331/100000000000000 : ℝ)*(f.sum) + (385390684546123/104735000000000000000000000000 : ℝ)*base65 + (301987271838375297/327296875000000000000000000000000 : ℝ)*base68 + (3691221169033406547/327296875000000000000000000000000 : ℝ)*base70 + (899183106881812203/327296875000000000000000000000000 : ℝ)*base71 + (44820527277207/104735000000000000000000000000 : ℝ)*base74 + (1112416730986054539/163648437500000000000000000000000 : ℝ)*base75 + (3106328974582062797/327296875000000000000000000000000 : ℝ)*base78 + (1174413862815976711/163648437500000000000000000000000 : ℝ)*base80 + (422903021284987/104735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (251077/10000000000000000000000 : ℝ)*base90 + (251077/10000000000000000000000 : ℝ)*base92 + (251077/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (973772410954038726672741111/327296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7657097/1562500000000 : ℝ)*(base19) + (76936411/20000000000000 : ℝ)*(base23) + (159206231/100000000000000 : ℝ)*(upper2) + (40740693/20000000000000 : ℝ)*(upper3) + (2574177/25000000000000 : ℝ)*(upper5) + (907257452992199/50000000000000 : ℝ)*(major0) + (907257452992199/50000000000000 : ℝ)*(major1) + (907257452992199/50000000000000 : ℝ)*(major2) + (940738027/20000000000000 : ℝ)*(sp1) + (1010476763/25000000000000 : ℝ)*(sp2) + (2554799635356873/100000000000000 : ℝ)*(sp4) + (255479444161253/10000000000000 : ℝ)*(sp5) + (1277397604383883/50000000000000 : ℝ)*(sp6) + (134278759679839/12500000000000 : ℝ)*(sp7) + (134278759679839/12500000000000 : ℝ)*(f.failure) + (2554799635356873/100000000000000 : ℝ)*(f.sum) + (104474484600369/52367500000000000000000000000 : ℝ)*base66 + (440326865529227731/40912109375000000000000000000000 : ℝ)*base68 + (385693401481899973/327296875000000000000000000000000 : ℝ)*base70 + (1960401820150962473/327296875000000000000000000000000 : ℝ)*base72 + (309131408652833/104735000000000000000000000000 : ℝ)*base74 + (129096612952939837/81824218750000000000000000000000 : ℝ)*base76 + (1215217040955649973/327296875000000000000000000000000 : ℝ)*base78 + (3615454823021837473/327296875000000000000000000000000 : ℝ)*base80 + (96857760713193/26183750000000000000000000000 : ℝ)*base81 + (10477179/1250000000000000000000 : ℝ)*base89 + (10477179/1250000000000000000000 : ℝ)*base91 + (10477179/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1581_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1837/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2207/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1581_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1581_s2_0 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-176851007/1000000000 : ℝ)*x 0 + (2719367333/5000000000 : ℝ)*x 1 + (2603764951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176851007/1000000000 : ℝ)^4659 ≤ (43422450461/400000000000 : ℝ)^3635 := by
    have hnat : (176851007 : ℕ)^4659*400000000000^3635 ≤ 43422450461^3635*1000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176851007 1000000000 43422450461 400000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719367333/5000000000 : ℝ)^4659 ≤ (22906362801673/50000000000000 : ℝ)^3635 := by
    have hnat : (2719367333 : ℕ)^4659*50000000000000^3635 ≤ 22906362801673^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719367333 5000000000 22906362801673 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2603764951/5000000000 : ℝ)^4659 ≤ (21665830885599/50000000000000 : ℝ)^3635 := by
    have hnat : (2603764951 : ℕ)^4659*50000000000000^3635 ≤ 21665830885599^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603764951 5000000000 21665830885599 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176851007/1000000000 : ℝ), (2719367333/5000000000 : ℝ), (2603764951/5000000000 : ℝ)] ![(43422450461/400000000000 : ℝ), (22906362801673/50000000000000 : ℝ), (21665830885599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176851007/1000000000 : ℝ)|^4659 ≤ (43422450461/400000000000 : ℝ)^3635
        have hw : |(-176851007/1000000000 : ℝ)|=(176851007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719367333/5000000000 : ℝ)|^4659 ≤ (22906362801673/50000000000000 : ℝ)^3635
        have hw : |(2719367333/5000000000 : ℝ)|=(2719367333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2603764951/5000000000 : ℝ)|^4659 ≤ (21665830885599/50000000000000 : ℝ)^3635
        have hw : |(2603764951/5000000000 : ℝ)|=(2603764951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s2_1 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070259523/2000000000 : ℝ)*x 0 + (-1887120937/10000000000 : ℝ)*x 1 + (1041506149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070259523/2000000000 : ℝ)^4659 ≤ (5608858924843/12500000000000 : ℝ)^3635 := by
    have hnat : (1070259523 : ℕ)^4659*12500000000000^3635 ≤ 5608858924843^3635*2000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070259523 2000000000 5608858924843 12500000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1887120937/10000000000 : ℝ)^4659 ≤ (1474682228623/12500000000000 : ℝ)^3635 := by
    have hnat : (1887120937 : ℕ)^4659*12500000000000^3635 ≤ 1474682228623^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887120937 10000000000 1474682228623 12500000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041506149/2000000000 : ℝ)^4659 ≤ (21665835380907/50000000000000 : ℝ)^3635 := by
    have hnat : (1041506149 : ℕ)^4659*50000000000000^3635 ≤ 21665835380907^3635*2000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041506149 2000000000 21665835380907 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070259523/2000000000 : ℝ), (-1887120937/10000000000 : ℝ), (1041506149/2000000000 : ℝ)] ![(5608858924843/12500000000000 : ℝ), (1474682228623/12500000000000 : ℝ), (21665835380907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070259523/2000000000 : ℝ)|^4659 ≤ (5608858924843/12500000000000 : ℝ)^3635
        have hw : |(1070259523/2000000000 : ℝ)|=(1070259523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1887120937/10000000000 : ℝ)|^4659 ≤ (1474682228623/12500000000000 : ℝ)^3635
        have hw : |(-1887120937/10000000000 : ℝ)|=(1887120937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041506149/2000000000 : ℝ)|^4659 ≤ (21665835380907/50000000000000 : ℝ)^3635
        have hw : |(1041506149/2000000000 : ℝ)|=(1041506149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s2_2 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351298121/10000000000 : ℝ)*x 0 + (2603764871/5000000000 : ℝ)*x 1 + (-1887121593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351298121/10000000000 : ℝ)^4659 ≤ (44870876836807/100000000000000 : ℝ)^3635 := by
    have hnat : (5351298121 : ℕ)^4659*100000000000000^3635 ≤ 44870876836807^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351298121 10000000000 44870876836807 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603764871/5000000000 : ℝ)^4659 ≤ (21665830032397/50000000000000 : ℝ)^3635 := by
    have hnat : (2603764871 : ℕ)^4659*50000000000000^3635 ≤ 21665830032397^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603764871 5000000000 21665830032397 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1887121593/10000000000 : ℝ)^4659 ≤ (11797463085293/100000000000000 : ℝ)^3635 := by
    have hnat : (1887121593 : ℕ)^4659*100000000000000^3635 ≤ 11797463085293^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887121593 10000000000 11797463085293 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351298121/10000000000 : ℝ), (2603764871/5000000000 : ℝ), (-1887121593/10000000000 : ℝ)] ![(44870876836807/100000000000000 : ℝ), (21665830032397/50000000000000 : ℝ), (11797463085293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351298121/10000000000 : ℝ)|^4659 ≤ (44870876836807/100000000000000 : ℝ)^3635
        have hw : |(5351298121/10000000000 : ℝ)|=(5351298121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603764871/5000000000 : ℝ)|^4659 ≤ (21665830032397/50000000000000 : ℝ)^3635
        have hw : |(2603764871/5000000000 : ℝ)|=(2603764871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1887121593/10000000000 : ℝ)|^4659 ≤ (11797463085293/100000000000000 : ℝ)^3635
        have hw : |(-1887121593/10000000000 : ℝ)|=(1887121593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s2_3 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4237258277/10000000000 : ℝ)*x 0 + (15877937/40000000 : ℝ)*x 1 + (4519348161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237258277/10000000000 : ℝ)^4659 ≤ (16634228562807/50000000000000 : ℝ)^3635 := by
    have hnat : (4237258277 : ℕ)^4659*50000000000000^3635 ≤ 16634228562807^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237258277 10000000000 16634228562807 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15877937/40000000 : ℝ)^4659 ≤ (6119630591907/20000000000000 : ℝ)^3635 := by
    have hnat : (15877937 : ℕ)^4659*20000000000000^3635 ≤ 6119630591907^3635*40000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15877937 40000000 6119630591907 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519348161/10000000000 : ℝ)^4659 ≤ (18066694946901/50000000000000 : ℝ)^3635 := by
    have hnat : (4519348161 : ℕ)^4659*50000000000000^3635 ≤ 18066694946901^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519348161 10000000000 18066694946901 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237258277/10000000000 : ℝ), (15877937/40000000 : ℝ), (4519348161/10000000000 : ℝ)] ![(16634228562807/50000000000000 : ℝ), (6119630591907/20000000000000 : ℝ), (18066694946901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237258277/10000000000 : ℝ)|^4659 ≤ (16634228562807/50000000000000 : ℝ)^3635
        have hw : |(4237258277/10000000000 : ℝ)|=(4237258277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15877937/40000000 : ℝ)|^4659 ≤ (6119630591907/20000000000000 : ℝ)^3635
        have hw : |(15877937/40000000 : ℝ)|=(15877937/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519348161/10000000000 : ℝ)|^4659 ≤ (18066694946901/50000000000000 : ℝ)^3635
        have hw : |(4519348161/10000000000 : ℝ)|=(4519348161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s2_4 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-884273963/5000000000 : ℝ)*x 0 + (2604448897/5000000000 : ℝ)*x 1 + (2718677863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (884273963/5000000000 : ℝ)^4659 ≤ (2713977611773/25000000000000 : ℝ)^3635 := by
    have hnat : (884273963 : ℕ)^4659*25000000000000^3635 ≤ 2713977611773^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884273963 5000000000 2713977611773 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2604448897/5000000000 : ℝ)^4659 ≤ (43346250912951/100000000000000 : ℝ)^3635 := by
    have hnat : (2604448897 : ℕ)^4659*100000000000000^3635 ≤ 43346250912951^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2604448897 5000000000 43346250912951 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718677863/5000000000 : ℝ)^4659 ≤ (45797838629923/100000000000000 : ℝ)^3635 := by
    have hnat : (2718677863 : ℕ)^4659*100000000000000^3635 ≤ 45797838629923^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718677863 5000000000 45797838629923 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-884273963/5000000000 : ℝ), (2604448897/5000000000 : ℝ), (2718677863/5000000000 : ℝ)] ![(2713977611773/25000000000000 : ℝ), (43346250912951/100000000000000 : ℝ), (45797838629923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-884273963/5000000000 : ℝ)|^4659 ≤ (2713977611773/25000000000000 : ℝ)^3635
        have hw : |(-884273963/5000000000 : ℝ)|=(884273963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2604448897/5000000000 : ℝ)|^4659 ≤ (43346250912951/100000000000000 : ℝ)^3635
        have hw : |(2604448897/5000000000 : ℝ)|=(2604448897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718677863/5000000000 : ℝ)|^4659 ≤ (45797838629923/100000000000000 : ℝ)^3635
        have hw : |(2718677863/5000000000 : ℝ)|=(2718677863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s2_5 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290044481/10000000000 : ℝ)*x 0 + (-207162033/1250000000 : ℝ)*x 1 + (1087471357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290044481/10000000000 : ℝ)^4659 ≤ (22106819233609/50000000000000 : ℝ)^3635 := by
    have hnat : (5290044481 : ℕ)^4659*50000000000000^3635 ≤ 22106819233609^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290044481 10000000000 22106819233609 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207162033/1250000000 : ℝ)^4659 ≤ (9988511447751/100000000000000 : ℝ)^3635 := by
    have hnat : (207162033 : ℕ)^4659*100000000000000^3635 ≤ 9988511447751^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207162033 1250000000 9988511447751 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087471357/2000000000 : ℝ)^4659 ≤ (45797850062431/100000000000000 : ℝ)^3635 := by
    have hnat : (1087471357 : ℕ)^4659*100000000000000^3635 ≤ 45797850062431^3635*2000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087471357 2000000000 45797850062431 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290044481/10000000000 : ℝ), (-207162033/1250000000 : ℝ), (1087471357/2000000000 : ℝ)] ![(22106819233609/50000000000000 : ℝ), (9988511447751/100000000000000 : ℝ), (45797850062431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290044481/10000000000 : ℝ)|^4659 ≤ (22106819233609/50000000000000 : ℝ)^3635
        have hw : |(5290044481/10000000000 : ℝ)|=(5290044481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207162033/1250000000 : ℝ)|^4659 ≤ (9988511447751/100000000000000 : ℝ)^3635
        have hw : |(-207162033/1250000000 : ℝ)|=(207162033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087471357/2000000000 : ℝ)|^4659 ≤ (45797850062431/100000000000000 : ℝ)^3635
        have hw : |(1087471357/2000000000 : ℝ)|=(1087471357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s2_6 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290045013/10000000000 : ℝ)*x 0 + (5437357953/10000000000 : ℝ)*x 1 + (-207161737/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290045013/10000000000 : ℝ)^4659 ≤ (8842728833239/20000000000000 : ℝ)^3635 := by
    have hnat : (5290045013 : ℕ)^4659*20000000000000^3635 ≤ 8842728833239^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290045013 10000000000 8842728833239 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437357953/10000000000 : ℝ)^4659 ≤ (5724732833957/12500000000000 : ℝ)^3635 := by
    have hnat : (5437357953 : ℕ)^4659*12500000000000^3635 ≤ 5724732833957^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437357953 10000000000 5724732833957 12500000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207161737/1250000000 : ℝ)^4659 ≤ (9988493155357/100000000000000 : ℝ)^3635 := by
    have hnat : (207161737 : ℕ)^4659*100000000000000^3635 ≤ 9988493155357^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207161737 1250000000 9988493155357 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290045013/10000000000 : ℝ), (5437357953/10000000000 : ℝ), (-207161737/1250000000 : ℝ)] ![(8842728833239/20000000000000 : ℝ), (5724732833957/12500000000000 : ℝ), (9988493155357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290045013/10000000000 : ℝ)|^4659 ≤ (8842728833239/20000000000000 : ℝ)^3635
        have hw : |(5290045013/10000000000 : ℝ)|=(5290045013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437357953/10000000000 : ℝ)|^4659 ≤ (5724732833957/12500000000000 : ℝ)^3635
        have hw : |(5437357953/10000000000 : ℝ)|=(5437357953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207161737/1250000000 : ℝ)|^4659 ≤ (9988493155357/100000000000000 : ℝ)^3635
        have hw : |(-207161737/1250000000 : ℝ)|=(207161737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s2_7 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4237350353/10000000000 : ℝ)*x 0 + (4516096461/10000000000 : ℝ)*x 1 + (3972762477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237350353/10000000000 : ℝ)^4659 ≤ (33269383707471/100000000000000 : ℝ)^3635 := by
    have hnat : (4237350353 : ℕ)^4659*100000000000000^3635 ≤ 33269383707471^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237350353 10000000000 33269383707471 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516096461/10000000000 : ℝ)^4659 ≤ (18050035612149/50000000000000 : ℝ)^3635 := by
    have hnat : (4516096461 : ℕ)^4659*50000000000000^3635 ≤ 18050035612149^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516096461 10000000000 18050035612149 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3972762477/10000000000 : ℝ)^4659 ≤ (15315272524097/50000000000000 : ℝ)^3635 := by
    have hnat : (3972762477 : ℕ)^4659*50000000000000^3635 ≤ 15315272524097^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3972762477 10000000000 15315272524097 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237350353/10000000000 : ℝ), (4516096461/10000000000 : ℝ), (3972762477/10000000000 : ℝ)] ![(33269383707471/100000000000000 : ℝ), (18050035612149/50000000000000 : ℝ), (15315272524097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237350353/10000000000 : ℝ)|^4659 ≤ (33269383707471/100000000000000 : ℝ)^3635
        have hw : |(4237350353/10000000000 : ℝ)|=(4237350353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516096461/10000000000 : ℝ)|^4659 ≤ (18050035612149/50000000000000 : ℝ)^3635
        have hw : |(4516096461/10000000000 : ℝ)|=(4516096461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3972762477/10000000000 : ℝ)|^4659 ≤ (15315272524097/50000000000000 : ℝ)^3635
        have hw : |(3972762477/10000000000 : ℝ)|=(3972762477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1581_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2207/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (68/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15783/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (9191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2207/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2207/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2207/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2207/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2207/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9191/100000 : ℝ) ^ (4657/1024 : ℝ) ≤ (482467145674589/25000000000000000000 : ℝ) := by
    have hpowers : (9191/100000 : ℝ)^4657 ≤ (482467145674589/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9191 : ℕ)^4657*25000000000000000000^1024 ≤ 482467145674589^1024*100000^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9191 100000 482467145674589 25000000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9191/100000 : ℝ)) (X := (482467145674589/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2207/12500 : ℝ) ^ (4657/1024 : ℝ) ≤ (37581841922513353/100000000000000000000 : ℝ) := by
    have hpowers : (2207/12500 : ℝ)^4657 ≤ (37581841922513353/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2207 : ℕ)^4657*100000000000000000000^1024 ≤ 37581841922513353^1024*12500^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2207 12500 37581841922513353 100000000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2207/12500 : ℝ)) (X := (37581841922513353/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500482467145674589/12500000000000000000 : ℝ) ≤ (125001060852307/125000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (12500482467145674589/12500000000000000000 : ℝ)^1024 ≤ (125001060852307/125000000000000 : ℝ)^4657 := by
      have hnat : (12500482467145674589 : ℕ)^1024*125000000000000^4657 ≤ 125001060852307^4657*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500482467145674589 12500000000000000000 125001060852307 125000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125001060852307/125000000000000 : ℝ)) (X := (12500482467145674589/12500000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039511710505211709/100000000000000000000 : ℝ) ≤ (5000434332804193/5000000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (100039511710505211709/100000000000000000000 : ℝ)^1024 ≤ (5000434332804193/5000000000000000 : ℝ)^4657 := by
      have hnat : (100039511710505211709 : ℕ)^1024*5000000000000000^4657 ≤ 5000434332804193^4657*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039511710505211709 100000000000000000000 5000434332804193 5000000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000434332804193/5000000000000000 : ℝ)) (X := (100039511710505211709/100000000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037581841922513353/50000000000000000000 : ℝ) ≤ (2500413115758053/2500000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (50037581841922513353/50000000000000000000 : ℝ)^1024 ≤ (2500413115758053/2500000000000000 : ℝ)^4657 := by
      have hnat : (50037581841922513353 : ℕ)^1024*2500000000000000^4657 ≤ 2500413115758053^4657*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037581841922513353 50000000000000000000 2500413115758053 2500000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500413115758053/2500000000000000 : ℝ)) (X := (50037581841922513353/50000000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(482467145674589/25000000000000000000 : ℝ) ≤ ((21159077661234382717/21162500000000000000 : ℝ)+2*(391898711913/423250000000000 : ℝ)*(9191/100000 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (21159077661234382717/21162500000000000000 : ℝ)+2*(391898711913/423250000000000 : ℝ)*(9191/100000 : ℝ)=(125001060852307/125000000000000 : ℝ) by norm_num, show 1+2*(482467145674589/25000000000000000000 : ℝ)=(12500482467145674589/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37581841922513353/100000000000000000000 : ℝ)+(482467145674589/25000000000000000000 : ℝ) ≤ ((21159077661234382717/21162500000000000000 : ℝ)+(391898711913/423250000000000 : ℝ)*((2207/12500 : ℝ)+(9191/100000 : ℝ)))^(4657/1024 : ℝ) := by
    rw [show (21159077661234382717/21162500000000000000 : ℝ)+(391898711913/423250000000000 : ℝ)*((2207/12500 : ℝ)+(9191/100000 : ℝ))=(5000434332804193/5000000000000000 : ℝ) by norm_num, show 1+(37581841922513353/100000000000000000000 : ℝ)+(482467145674589/25000000000000000000 : ℝ)=(100039511710505211709/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37581841922513353/100000000000000000000 : ℝ) ≤ ((21159077661234382717/21162500000000000000 : ℝ)+2*(391898711913/423250000000000 : ℝ)*(2207/12500 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (21159077661234382717/21162500000000000000 : ℝ)+2*(391898711913/423250000000000 : ℝ)*(2207/12500 : ℝ)=(2500413115758053/2500000000000000 : ℝ) by norm_num, show 1+2*(37581841922513353/100000000000000000000 : ℝ)=(50037581841922513353/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21159077661234382717/21162500000000000000 : ℝ)*(X 1 0+X 2 0)+(391898711913/423250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (9191/100000 : ℝ)) (hi := (2207/12500 : ℝ)) (c := (21159077661234382717/21162500000000000000 : ℝ)) (alpha := (391898711913/423250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21159077661234382717/21162500000000000000 : ℝ)*(X 0 1+X 2 1)+(391898711913/423250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (9191/100000 : ℝ)) (hi := (2207/12500 : ℝ)) (c := (21159077661234382717/21162500000000000000 : ℝ)) (alpha := (391898711913/423250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21159077661234382717/21162500000000000000 : ℝ)*(X 0 2+X 1 2)+(391898711913/423250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (9191/100000 : ℝ)) (hi := (2207/12500 : ℝ)) (c := (21159077661234382717/21162500000000000000 : ℝ)) (alpha := (391898711913/423250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-176851007/1000000000 : ℝ)*X 0 0+(2719367333/5000000000 : ℝ)*X 0 1+(2603764951/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070259523/2000000000 : ℝ)*X 1 0+(-1887120937/10000000000 : ℝ)*X 1 1+(1041506149/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351298121/10000000000 : ℝ)*X 2 0+(2603764871/5000000000 : ℝ)*X 2 1+(-1887121593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4237258277/10000000000 : ℝ)*X 0 0+(15877937/40000000 : ℝ)*X 0 1+(4519348161/10000000000 : ℝ)*X 0 2+(4237258277/10000000000 : ℝ)*X 1 0+(15877937/40000000 : ℝ)*X 1 1+(4519348161/10000000000 : ℝ)*X 1 2+(4237258277/10000000000 : ℝ)*X 2 0+(15877937/40000000 : ℝ)*X 2 1+(4519348161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-884273963/5000000000 : ℝ)*X 0 0+(2604448897/5000000000 : ℝ)*X 0 1+(2718677863/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290044481/10000000000 : ℝ)*X 1 0+(-207162033/1250000000 : ℝ)*X 1 1+(1087471357/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290045013/10000000000 : ℝ)*X 2 0+(5437357953/10000000000 : ℝ)*X 2 1+(-207161737/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4237350353/10000000000 : ℝ)*X 0 0+(4516096461/10000000000 : ℝ)*X 0 1+(3972762477/10000000000 : ℝ)*X 0 2+(4237350353/10000000000 : ℝ)*X 1 0+(4516096461/10000000000 : ℝ)*X 1 1+(3972762477/10000000000 : ℝ)*X 1 2+(4237350353/10000000000 : ℝ)*X 2 0+(4516096461/10000000000 : ℝ)*X 2 1+(3972762477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4717593014448469875507026283/529062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118174029/20000000000000 : ℝ)*(base19) + (1129332779/100000000000000 : ℝ)*(base23) + (107689777/100000000000000 : ℝ)*(upper2) + (107775247/100000000000000 : ℝ)*(upper3) + (1535967245767333/50000000000000 : ℝ)*(major0) + (1535967245767333/50000000000000 : ℝ)*(major1) + (1535967245767333/50000000000000 : ℝ)*(major2) + (432519690152243/10000000000000 : ℝ)*(sp0) + (1081304951823801/25000000000000 : ℝ)*(sp1) + (432521300000941/10000000000000 : ℝ)*(sp2) + (363727872405919/20000000000000 : ℝ)*(sp3) + (23496642917/100000000000000 : ℝ)*(sp4) + (6268823159/100000000000000 : ℝ)*(sp6) + (4462822329/50000000000000 : ℝ)*(sp7) + (1818648287674253/100000000000000 : ℝ)*(f.failure) + (1081305099541337/25000000000000 : ℝ)*(f.sum) + (231062171822159/42325000000000000000000000000 : ℝ)*base66 + (9018632209636083761/1058125000000000000000000000000000 : ℝ)*base67 + (901967280247958761/1058125000000000000000000000000000 : ℝ)*base69 + (3566487490500791239/1058125000000000000000000000000000 : ℝ)*base72 + (632067946613/1322656250000000000000000000 : ℝ)*base73 + (20308203767223291239/1058125000000000000000000000000000 : ℝ)*base76 + (7371543312613916239/1058125000000000000000000000000000 : ℝ)*base78 + (5170318541249541239/1058125000000000000000000000000000 : ℝ)*base80 + (118219252141341/42325000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (45118433/10000000000000000000000 : ℝ)*base89 + (45118433/10000000000000000000000 : ℝ)*base91 + (45118433/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2548577356829326225659103671/1058125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (203062859/100000000000000 : ℝ)*(base8) + (1006763521/100000000000000 : ℝ)*(base15) + (48896527/100000000000000 : ℝ)*(base29) + (9624439/25000000000000 : ℝ)*(lower2) + (22652853/100000000000000 : ℝ)*(lower4) + (194301909208497/6250000000000 : ℝ)*(major0) + (1554415298116239/50000000000000 : ℝ)*(major1) + (3108830596232479/100000000000000 : ℝ)*(major2) + (20991638739/50000000000000 : ℝ)*(sp2) + (583786173/25000000000000 : ℝ)*(sp3) + (2188584684980637/50000000000000 : ℝ)*(sp4) + (2188584258682043/50000000000000 : ℝ)*(sp5) + (273570471303133/6250000000000 : ℝ)*(sp6) + (920244602005081/50000000000000 : ℝ)*(sp7) + (920245769577427/50000000000000 : ℝ)*(f.failure) + (2188584786512067/50000000000000 : ℝ)*(f.sum) + (22285077128291/42325000000000000000000000000 : ℝ)*base65 + (3833819739928066363/1058125000000000000000000000000000 : ℝ)*base67 + (11392732955749865443/2116250000000000000000000000000000 : ℝ)*base69 + (255969100527767319/33066406250000000000000000000000 : ℝ)*base72 + (103325352374653/42325000000000000000000000000 : ℝ)*base73 + (2911487284915465443/2116250000000000000000000000000000 : ℝ)*base75 + (1747461376660452599/132265625000000000000000000000000 : ℝ)*base77 + (1936407211395708637/1058125000000000000000000000000000 : ℝ)*base80 + (8498602135679/4232500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (78925953/5000000000000000000000 : ℝ)*base90 + (28925953/5000000000000000000000 : ℝ)*base92 + (78925953/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1581_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2207/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15783/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1581_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1581_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15783/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1581_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1581_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1581_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15783/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1581_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
