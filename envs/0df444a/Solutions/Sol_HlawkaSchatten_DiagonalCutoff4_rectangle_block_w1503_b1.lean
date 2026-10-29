-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1503_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:53:04.716196+00:00
-- url     : https://prove2.me/submissions/8faace98-c0c8-48e5-83d1-cda00f9bb0b5

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
theorem support_rectangle_w1503_s3_0 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1880843353/10000000000 : ℝ)*x 0 + (5438032429/10000000000 : ℝ)*x 1 + (521390751/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1880843353/10000000000 : ℝ)^4503 ≤ (11501842776521/100000000000000 : ℝ)^3479 := by
    have hnat : (1880843353 : ℕ)^4503*100000000000000^3479 ≤ 11501842776521^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880843353 10000000000 11501842776521 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438032429/10000000000 : ℝ)^4503 ≤ (45454031047303/100000000000000 : ℝ)^3479 := by
    have hnat : (5438032429 : ℕ)^4503*100000000000000^3479 ≤ 45454031047303^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438032429 10000000000 45454031047303 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521390751/1000000000 : ℝ)^4503 ≤ (8608825233159/20000000000000 : ℝ)^3479 := by
    have hnat : (521390751 : ℕ)^4503*20000000000000^3479 ≤ 8608825233159^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521390751 1000000000 8608825233159 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1880843353/10000000000 : ℝ), (5438032429/10000000000 : ℝ), (521390751/1000000000 : ℝ)] ![(11501842776521/100000000000000 : ℝ), (45454031047303/100000000000000 : ℝ), (8608825233159/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1880843353/10000000000 : ℝ)|^4503 ≤ (11501842776521/100000000000000 : ℝ)^3479
        have hw : |(-1880843353/10000000000 : ℝ)|=(1880843353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438032429/10000000000 : ℝ)|^4503 ≤ (45454031047303/100000000000000 : ℝ)^3479
        have hw : |(5438032429/10000000000 : ℝ)|=(5438032429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521390751/1000000000 : ℝ)|^4503 ≤ (8608825233159/20000000000000 : ℝ)^3479
        have hw : |(521390751/1000000000 : ℝ)|=(521390751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s3_1 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676516487/5000000000 : ℝ)*x 0 + (-997868347/5000000000 : ℝ)*x 1 + (5213907623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676516487/5000000000 : ℝ)^4503 ≤ (22268282085823/50000000000000 : ℝ)^3479 := by
    have hnat : (2676516487 : ℕ)^4503*50000000000000^3479 ≤ 22268282085823^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676516487 5000000000 22268282085823 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997868347/5000000000 : ℝ)^4503 ≤ (6209654221133/50000000000000 : ℝ)^3479 := by
    have hnat : (997868347 : ℕ)^4503*50000000000000^3479 ≤ 6209654221133^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997868347 5000000000 6209654221133 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5213907623/10000000000 : ℝ)^4503 ≤ (21522063686633/50000000000000 : ℝ)^3479 := by
    have hnat : (5213907623 : ℕ)^4503*50000000000000^3479 ≤ 21522063686633^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213907623 10000000000 21522063686633 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676516487/5000000000 : ℝ), (-997868347/5000000000 : ℝ), (5213907623/10000000000 : ℝ)] ![(22268282085823/50000000000000 : ℝ), (6209654221133/50000000000000 : ℝ), (21522063686633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676516487/5000000000 : ℝ)|^4503 ≤ (22268282085823/50000000000000 : ℝ)^3479
        have hw : |(2676516487/5000000000 : ℝ)|=(2676516487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-997868347/5000000000 : ℝ)|^4503 ≤ (6209654221133/50000000000000 : ℝ)^3479
        have hw : |(-997868347/5000000000 : ℝ)|=(997868347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5213907623/10000000000 : ℝ)|^4503 ≤ (21522063686633/50000000000000 : ℝ)^3479
        have hw : |(5213907623/10000000000 : ℝ)|=(5213907623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s3_2 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070606731/2000000000 : ℝ)*x 0 + (65173837/125000000 : ℝ)*x 1 + (-249467083/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070606731/2000000000 : ℝ)^4503 ≤ (44536571505149/100000000000000 : ℝ)^3479 := by
    have hnat : (1070606731 : ℕ)^4503*100000000000000^3479 ≤ 44536571505149^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070606731 2000000000 44536571505149 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65173837/125000000 : ℝ)^4503 ≤ (21522060144363/50000000000000 : ℝ)^3479 := by
    have hnat : (65173837 : ℕ)^4503*50000000000000^3479 ≤ 21522060144363^3479*125000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65173837 125000000 21522060144363 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249467083/1250000000 : ℝ)^4503 ≤ (12419308200629/100000000000000 : ℝ)^3479 := by
    have hnat : (249467083 : ℕ)^4503*100000000000000^3479 ≤ 12419308200629^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249467083 1250000000 12419308200629 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070606731/2000000000 : ℝ), (65173837/125000000 : ℝ), (-249467083/1250000000 : ℝ)] ![(44536571505149/100000000000000 : ℝ), (21522060144363/50000000000000 : ℝ), (12419308200629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070606731/2000000000 : ℝ)|^4503 ≤ (44536571505149/100000000000000 : ℝ)^3479
        have hw : |(1070606731/2000000000 : ℝ)|=(1070606731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65173837/125000000 : ℝ)|^4503 ≤ (21522060144363/50000000000000 : ℝ)^3479
        have hw : |(65173837/125000000 : ℝ)|=(65173837/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249467083/1250000000 : ℝ)|^4503 ≤ (12419308200629/100000000000000 : ℝ)^3479
        have hw : |(-249467083/1250000000 : ℝ)|=(249467083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s3_3 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273636549/10000000000 : ℝ)*x 0 + (4027514619/10000000000 : ℝ)*x 1 + (4532517181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273636549/10000000000 : ℝ)^4503 ≤ (33275721915263/100000000000000 : ℝ)^3479 := by
    have hnat : (4273636549 : ℕ)^4503*100000000000000^3479 ≤ 33275721915263^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273636549 10000000000 33275721915263 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4027514619/10000000000 : ℝ)^4503 ≤ (30816602668621/100000000000000 : ℝ)^3479 := by
    have hnat : (4027514619 : ℕ)^4503*100000000000000^3479 ≤ 30816602668621^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027514619 10000000000 30816602668621 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532517181/10000000000 : ℝ)^4503 ≤ (17953837700319/50000000000000 : ℝ)^3479 := by
    have hnat : (4532517181 : ℕ)^4503*50000000000000^3479 ≤ 17953837700319^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532517181 10000000000 17953837700319 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273636549/10000000000 : ℝ), (4027514619/10000000000 : ℝ), (4532517181/10000000000 : ℝ)] ![(33275721915263/100000000000000 : ℝ), (30816602668621/100000000000000 : ℝ), (17953837700319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273636549/10000000000 : ℝ)|^4503 ≤ (33275721915263/100000000000000 : ℝ)^3479
        have hw : |(4273636549/10000000000 : ℝ)|=(4273636549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4027514619/10000000000 : ℝ)|^4503 ≤ (30816602668621/100000000000000 : ℝ)^3479
        have hw : |(4027514619/10000000000 : ℝ)|=(4027514619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4532517181/10000000000 : ℝ)|^4503 ≤ (17953837700319/50000000000000 : ℝ)^3479
        have hw : |(4532517181/10000000000 : ℝ)|=(4532517181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s3_4 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-117554653/625000000 : ℝ)*x 0 + (325943477/625000000 : ℝ)*x 1 + (5436836107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117554653/625000000 : ℝ)^4503 ≤ (2300417780101/20000000000000 : ℝ)^3479 := by
    have hnat : (117554653 : ℕ)^4503*20000000000000^3479 ≤ 2300417780101^3479*625000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117554653 625000000 2300417780101 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325943477/625000000 : ℝ)^4503 ≤ (21528411181977/50000000000000 : ℝ)^3479 := by
    have hnat : (325943477 : ℕ)^4503*50000000000000^3479 ≤ 21528411181977^3479*625000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325943477 625000000 21528411181977 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436836107/10000000000 : ℝ)^4503 ≤ (45441088726603/100000000000000 : ℝ)^3479 := by
    have hnat : (5436836107 : ℕ)^4503*100000000000000^3479 ≤ 45441088726603^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436836107 10000000000 45441088726603 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117554653/625000000 : ℝ), (325943477/625000000 : ℝ), (5436836107/10000000000 : ℝ)] ![(2300417780101/20000000000000 : ℝ), (21528411181977/50000000000000 : ℝ), (45441088726603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117554653/625000000 : ℝ)|^4503 ≤ (2300417780101/20000000000000 : ℝ)^3479
        have hw : |(-117554653/625000000 : ℝ)|=(117554653/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325943477/625000000 : ℝ)|^4503 ≤ (21528411181977/50000000000000 : ℝ)^3479
        have hw : |(325943477/625000000 : ℝ)|=(325943477/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436836107/10000000000 : ℝ)|^4503 ≤ (45441088726603/100000000000000 : ℝ)^3479
        have hw : |(5436836107/10000000000 : ℝ)|=(5436836107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s3_5 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647138571/5000000000 : ℝ)*x 0 + (-88640387/500000000 : ℝ)*x 1 + (1087367231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647138571/5000000000 : ℝ)^4503 ≤ (43904863465539/100000000000000 : ℝ)^3479 := by
    have hnat : (2647138571 : ℕ)^4503*100000000000000^3479 ≤ 43904863465539^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647138571 5000000000 43904863465539 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88640387/500000000 : ℝ)^4503 ≤ (5327023636697/50000000000000 : ℝ)^3479 := by
    have hnat : (88640387 : ℕ)^4503*50000000000000^3479 ≤ 5327023636697^3479*500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88640387 500000000 5327023636697 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087367231/2000000000 : ℝ)^4503 ≤ (4544108924587/10000000000000 : ℝ)^3479 := by
    have hnat : (1087367231 : ℕ)^4503*10000000000000^3479 ≤ 4544108924587^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087367231 2000000000 4544108924587 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647138571/5000000000 : ℝ), (-88640387/500000000 : ℝ), (1087367231/2000000000 : ℝ)] ![(43904863465539/100000000000000 : ℝ), (5327023636697/50000000000000 : ℝ), (4544108924587/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647138571/5000000000 : ℝ)|^4503 ≤ (43904863465539/100000000000000 : ℝ)^3479
        have hw : |(2647138571/5000000000 : ℝ)|=(2647138571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88640387/500000000 : ℝ)|^4503 ≤ (5327023636697/50000000000000 : ℝ)^3479
        have hw : |(-88640387/500000000 : ℝ)|=(88640387/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087367231/2000000000 : ℝ)|^4503 ≤ (4544108924587/10000000000000 : ℝ)^3479
        have hw : |(1087367231/2000000000 : ℝ)|=(1087367231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s3_6 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294276957/10000000000 : ℝ)*x 0 + (217473449/400000000 : ℝ)*x 1 + (-1772807897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294276957/10000000000 : ℝ)^4503 ≤ (21952430739893/50000000000000 : ℝ)^3479 := by
    have hnat : (5294276957 : ℕ)^4503*50000000000000^3479 ≤ 21952430739893^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294276957 10000000000 21952430739893 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217473449/400000000 : ℝ)^4503 ≤ (710017031299/1562500000000 : ℝ)^3479 := by
    have hnat : (217473449 : ℕ)^4503*1562500000000^3479 ≤ 710017031299^3479*400000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217473449 400000000 710017031299 1562500000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1772807897/10000000000 : ℝ)^4503 ≤ (10654048494631/100000000000000 : ℝ)^3479 := by
    have hnat : (1772807897 : ℕ)^4503*100000000000000^3479 ≤ 10654048494631^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772807897 10000000000 10654048494631 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294276957/10000000000 : ℝ), (217473449/400000000 : ℝ), (-1772807897/10000000000 : ℝ)] ![(21952430739893/50000000000000 : ℝ), (710017031299/1562500000000 : ℝ), (10654048494631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294276957/10000000000 : ℝ)|^4503 ≤ (21952430739893/50000000000000 : ℝ)^3479
        have hw : |(5294276957/10000000000 : ℝ)|=(5294276957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217473449/400000000 : ℝ)|^4503 ≤ (710017031299/1562500000000 : ℝ)^3479
        have hw : |(217473449/400000000 : ℝ)|=(217473449/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1772807897/10000000000 : ℝ)|^4503 ≤ (10654048494631/100000000000000 : ℝ)^3479
        have hw : |(-1772807897/10000000000 : ℝ)|=(1772807897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s3_7 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (854741799/2000000000 : ℝ)*x 0 + (4529840553/10000000000 : ℝ)*x 1 + (4030211719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854741799/2000000000 : ℝ)^4503 ≤ (16638226016513/50000000000000 : ℝ)^3479 := by
    have hnat : (854741799 : ℕ)^4503*50000000000000^3479 ≤ 16638226016513^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854741799 2000000000 16638226016513 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4529840553/10000000000 : ℝ)^4503 ≤ (3588023151407/10000000000000 : ℝ)^3479 := by
    have hnat : (4529840553 : ℕ)^4503*10000000000000^3479 ≤ 3588023151407^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529840553 10000000000 3588023151407 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4030211719/10000000000 : ℝ)^4503 ≤ (7710829106747/25000000000000 : ℝ)^3479 := by
    have hnat : (4030211719 : ℕ)^4503*25000000000000^3479 ≤ 7710829106747^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030211719 10000000000 7710829106747 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854741799/2000000000 : ℝ), (4529840553/10000000000 : ℝ), (4030211719/10000000000 : ℝ)] ![(16638226016513/50000000000000 : ℝ), (3588023151407/10000000000000 : ℝ), (7710829106747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854741799/2000000000 : ℝ)|^4503 ≤ (16638226016513/50000000000000 : ℝ)^3479
        have hw : |(854741799/2000000000 : ℝ)|=(854741799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4529840553/10000000000 : ℝ)|^4503 ≤ (3588023151407/10000000000000 : ℝ)^3479
        have hw : |(4529840553/10000000000 : ℝ)|=(4529840553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4030211719/10000000000 : ℝ)|^4503 ≤ (7710829106747/25000000000000 : ℝ)^3479
        have hw : |(4030211719/10000000000 : ℝ)|=(4030211719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1503_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5187/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10811/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3889/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5187/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5187/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5187/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5187/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5187/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5187/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5187/50000 : ℝ) ^ (4501/1024 : ℝ) ≤ (2363491421941399/50000000000000000000 : ℝ) := by
    have hpowers : (5187/50000 : ℝ)^4501 ≤ (2363491421941399/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5187 : ℕ)^4501*50000000000000000000^1024 ≤ 2363491421941399^1024*50000^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5187 50000 2363491421941399 50000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5187/50000 : ℝ)) (X := (2363491421941399/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16031/100000 : ℝ) ^ (4501/1024 : ℝ) ≤ (16009146262598793/50000000000000000000 : ℝ) := by
    have hpowers : (16031/100000 : ℝ)^4501 ≤ (16009146262598793/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16031 : ℕ)^4501*50000000000000000000^1024 ≤ 16009146262598793^1024*100000^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16031 100000 16009146262598793 50000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16031/100000 : ℝ)) (X := (16009146262598793/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002363491421941399/25000000000000000000 : ℝ) ≤ (10000215074591881/10000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (25002363491421941399/25000000000000000000 : ℝ)^1024 ≤ (10000215074591881/10000000000000000 : ℝ)^4501 := by
      have hnat : (25002363491421941399 : ℕ)^1024*10000000000000000^4501 ≤ 10000215074591881^4501*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002363491421941399 25000000000000000000 10000215074591881 10000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000215074591881/10000000000000000 : ℝ)) (X := (25002363491421941399/25000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563074144927641881/1562500000000000000 : ℝ) ≤ (10000835854761169/10000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (1563074144927641881/1562500000000000000 : ℝ)^1024 ≤ (10000835854761169/10000000000000000 : ℝ)^4501 := by
      have hnat : (1563074144927641881 : ℕ)^1024*10000000000000000^4501 ≤ 10000835854761169^4501*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563074144927641881 1562500000000000000 10000835854761169 10000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000835854761169/10000000000000000 : ℝ)) (X := (1563074144927641881/1562500000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016009146262598793/25000000000000000000 : ℝ) ≤ (10001456634930457/10000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (25016009146262598793/25000000000000000000 : ℝ)^1024 ≤ (10001456634930457/10000000000000000 : ℝ)^4501 := by
      have hnat : (25016009146262598793 : ℕ)^1024*10000000000000000^4501 ≤ 10001456634930457^4501*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016009146262598793 25000000000000000000 10001456634930457 10000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001456634930457/10000000000000000 : ℝ)) (X := (25016009146262598793/25000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2363491421941399/50000000000000000000 : ℝ) ≤ ((56558336730013883393/56570000000000000000 : ℝ)+2*(77597521161/70712500000000 : ℝ)*(5187/50000 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (56558336730013883393/56570000000000000000 : ℝ)+2*(77597521161/70712500000000 : ℝ)*(5187/50000 : ℝ)=(10000215074591881/10000000000000000 : ℝ) by norm_num, show 1+2*(2363491421941399/50000000000000000000 : ℝ)=(25002363491421941399/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16009146262598793/50000000000000000000 : ℝ)+(2363491421941399/50000000000000000000 : ℝ) ≤ ((56558336730013883393/56570000000000000000 : ℝ)+(77597521161/70712500000000 : ℝ)*((16031/100000 : ℝ)+(5187/50000 : ℝ)))^(4501/1024 : ℝ) := by
    rw [show (56558336730013883393/56570000000000000000 : ℝ)+(77597521161/70712500000000 : ℝ)*((16031/100000 : ℝ)+(5187/50000 : ℝ))=(10000835854761169/10000000000000000 : ℝ) by norm_num, show 1+(16009146262598793/50000000000000000000 : ℝ)+(2363491421941399/50000000000000000000 : ℝ)=(1563074144927641881/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16009146262598793/50000000000000000000 : ℝ) ≤ ((56558336730013883393/56570000000000000000 : ℝ)+2*(77597521161/70712500000000 : ℝ)*(16031/100000 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (56558336730013883393/56570000000000000000 : ℝ)+2*(77597521161/70712500000000 : ℝ)*(16031/100000 : ℝ)=(10001456634930457/10000000000000000 : ℝ) by norm_num, show 1+2*(16009146262598793/50000000000000000000 : ℝ)=(25016009146262598793/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56558336730013883393/56570000000000000000 : ℝ)*(X 1 0+X 2 0)+(77597521161/70712500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (5187/50000 : ℝ)) (hi := (16031/100000 : ℝ)) (c := (56558336730013883393/56570000000000000000 : ℝ)) (alpha := (77597521161/70712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56558336730013883393/56570000000000000000 : ℝ)*(X 0 1+X 2 1)+(77597521161/70712500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (5187/50000 : ℝ)) (hi := (16031/100000 : ℝ)) (c := (56558336730013883393/56570000000000000000 : ℝ)) (alpha := (77597521161/70712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56558336730013883393/56570000000000000000 : ℝ)*(X 0 2+X 1 2)+(77597521161/70712500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (5187/50000 : ℝ)) (hi := (16031/100000 : ℝ)) (c := (56558336730013883393/56570000000000000000 : ℝ)) (alpha := (77597521161/70712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1880843353/10000000000 : ℝ)*X 0 0+(5438032429/10000000000 : ℝ)*X 0 1+(521390751/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676516487/5000000000 : ℝ)*X 1 0+(-997868347/5000000000 : ℝ)*X 1 1+(5213907623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070606731/2000000000 : ℝ)*X 2 0+(65173837/125000000 : ℝ)*X 2 1+(-249467083/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4273636549/10000000000 : ℝ)*X 0 0+(4027514619/10000000000 : ℝ)*X 0 1+(4532517181/10000000000 : ℝ)*X 0 2+(4273636549/10000000000 : ℝ)*X 1 0+(4027514619/10000000000 : ℝ)*X 1 1+(4532517181/10000000000 : ℝ)*X 1 2+(4273636549/10000000000 : ℝ)*X 2 0+(4027514619/10000000000 : ℝ)*X 2 1+(4532517181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-117554653/625000000 : ℝ)*X 0 0+(325943477/625000000 : ℝ)*X 0 1+(5436836107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647138571/5000000000 : ℝ)*X 1 0+(-88640387/500000000 : ℝ)*X 1 1+(1087367231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294276957/10000000000 : ℝ)*X 2 0+(217473449/400000000 : ℝ)*X 2 1+(-1772807897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((854741799/2000000000 : ℝ)*X 0 0+(4529840553/10000000000 : ℝ)*X 0 1+(4030211719/10000000000 : ℝ)*X 0 2+(854741799/2000000000 : ℝ)*X 1 0+(4529840553/10000000000 : ℝ)*X 1 1+(4030211719/10000000000 : ℝ)*X 1 2+(854741799/2000000000 : ℝ)*X 2 0+(4529840553/10000000000 : ℝ)*X 2 1+(4030211719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92929781109140243003610423/56570000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (880485389/50000000000000 : ℝ)*(base19) + (86794729/5000000000000 : ℝ)*(base23) + (421756659/100000000000000 : ℝ)*(upper3) + (317274491/100000000000000 : ℝ)*(upper4) + (125720887/100000000000000 : ℝ)*(upper5) + (128841038837763/4000000000000 : ℝ)*(major0) + (128841038837763/4000000000000 : ℝ)*(major1) + (128841038837763/4000000000000 : ℝ)*(major2) + (2230908941911623/50000000000000 : ℝ)*(sp0) + (2230918636090307/50000000000000 : ℝ)*(sp1) + (1115459324314203/25000000000000 : ℝ)*(sp2) + (495049329300941/25000000000000 : ℝ)*(sp3) + (21149328147/100000000000000 : ℝ)*(sp4) + (3107354999/20000000000000 : ℝ)*(sp7) + (49505321349469/2500000000000 : ℝ)*(f.failure) + (4461839033151393/100000000000000 : ℝ)*(f.sum) + (10160565928801/5657000000000000000000000000 : ℝ)*base65 + (2765059441042449859/226280000000000000000000000000000 : ℝ)*base67 + (634010169952470141/226280000000000000000000000000000 : ℝ)*base70 + (2517006800260209859/226280000000000000000000000000000 : ℝ)*base71 + (647168883189/226280000000000000000000000 : ℝ)*base73 + (3680144897776289859/226280000000000000000000000000000 : ℝ)*base75 + (1569246184325489859/226280000000000000000000000000000 : ℝ)*base77 + (1500649096847489859/226280000000000000000000000000000 : ℝ)*base79 + (1057274993577/5657000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (275117/250000000000000000000 : ℝ)*base89 + (275117/250000000000000000000 : ℝ)*base91 + (275117/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (174651410877707430482211/28285000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1086297701/100000000000000 : ℝ)*(base19) + (1316588967/100000000000000 : ℝ)*(base23) + (16852051/12500000000000 : ℝ)*(upper3) + (184402217/100000000000000 : ℝ)*(lower4) + (12439161/25000000000000 : ℝ)*(upper5) + (406953477858273/12500000000000 : ℝ)*(major0) + (406953477858273/12500000000000 : ℝ)*(major1) + (406953477858273/12500000000000 : ℝ)*(major2) + (686365133/4000000000000 : ℝ)*(sp1) + (20724611121/100000000000000 : ℝ)*(sp2) + (450977016137803/10000000000000 : ℝ)*(sp4) + (4509751915952003/100000000000000 : ℝ)*(sp5) + (2254874060088971/50000000000000 : ℝ)*(sp6) + (1000742639265487/50000000000000 : ℝ)*(sp7) + (1000742639265487/50000000000000 : ℝ)*(f.failure) + (450977016137803/10000000000000 : ℝ)*(f.sum) + (102125181067671/14142500000000000000000000000 : ℝ)*base65 + (2425546131506989711/707125000000000000000000000000000 : ℝ)*base68 + (4432692112336739711/707125000000000000000000000000000 : ℝ)*base70 + (782282925834510289/707125000000000000000000000000000 : ℝ)*base71 + (18046815809207/7071250000000000000000000000 : ℝ)*base74 + (3679968643962010289/707125000000000000000000000000000 : ℝ)*base75 + (5649836225148114711/707125000000000000000000000000000 : ℝ)*base78 + (7309382824674260289/707125000000000000000000000000000 : ℝ)*base79 + (3388172090897/7071250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (146209/5000000000000000000000 : ℝ)*base90 + (146209/5000000000000000000000 : ℝ)*base92 + (146209/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1503_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5187/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10811/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3889/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1503_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1503_s4_0 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1881327749/10000000000 : ℝ)*x 0 + (1086971337/2000000000 : ℝ)*x 1 + (5216763509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1881327749/10000000000 : ℝ)^4503 ≤ (11505677016807/100000000000000 : ℝ)^3479 := by
    have hnat : (1881327749 : ℕ)^4503*100000000000000^3479 ≤ 11505677016807^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881327749 10000000000 11505677016807 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086971337/2000000000 : ℝ)^4503 ≤ (9083935267513/20000000000000 : ℝ)^3479 := by
    have hnat : (1086971337 : ℕ)^4503*20000000000000^3479 ≤ 9083935267513^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086971337 2000000000 9083935267513 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216763509/10000000000 : ℝ)^4503 ≤ (43074646630809/100000000000000 : ℝ)^3479 := by
    have hnat : (5216763509 : ℕ)^4503*100000000000000^3479 ≤ 43074646630809^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216763509 10000000000 43074646630809 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1881327749/10000000000 : ℝ), (1086971337/2000000000 : ℝ), (5216763509/10000000000 : ℝ)] ![(11505677016807/100000000000000 : ℝ), (9083935267513/20000000000000 : ℝ), (43074646630809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1881327749/10000000000 : ℝ)|^4503 ≤ (11505677016807/100000000000000 : ℝ)^3479
        have hw : |(-1881327749/10000000000 : ℝ)|=(1881327749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086971337/2000000000 : ℝ)|^4503 ≤ (9083935267513/20000000000000 : ℝ)^3479
        have hw : |(1086971337/2000000000 : ℝ)|=(1086971337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216763509/10000000000 : ℝ)|^4503 ≤ (43074646630809/100000000000000 : ℝ)^3479
        have hw : |(5216763509/10000000000 : ℝ)|=(5216763509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s4_1 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676102217/5000000000 : ℝ)*x 0 + (-498264121/2500000000 : ℝ)*x 1 + (1043352449/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676102217/5000000000 : ℝ)^4503 ≤ (44527642055011/100000000000000 : ℝ)^3479 := by
    have hnat : (2676102217 : ℕ)^4503*100000000000000^3479 ≤ 44527642055011^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676102217 5000000000 44527642055011 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (498264121/2500000000 : ℝ)^4503 ≤ (12397724804613/100000000000000 : ℝ)^3479 := by
    have hnat : (498264121 : ℕ)^4503*100000000000000^3479 ≤ 12397724804613^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498264121 2500000000 12397724804613 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043352449/2000000000 : ℝ)^4503 ≤ (43074633122059/100000000000000 : ℝ)^3479 := by
    have hnat : (1043352449 : ℕ)^4503*100000000000000^3479 ≤ 43074633122059^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043352449 2000000000 43074633122059 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676102217/5000000000 : ℝ), (-498264121/2500000000 : ℝ), (1043352449/2000000000 : ℝ)] ![(44527642055011/100000000000000 : ℝ), (12397724804613/100000000000000 : ℝ), (43074633122059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676102217/5000000000 : ℝ)|^4503 ≤ (44527642055011/100000000000000 : ℝ)^3479
        have hw : |(2676102217/5000000000 : ℝ)|=(2676102217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-498264121/2500000000 : ℝ)|^4503 ≤ (12397724804613/100000000000000 : ℝ)^3479
        have hw : |(-498264121/2500000000 : ℝ)|=(498264121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043352449/2000000000 : ℝ)|^4503 ≤ (43074633122059/100000000000000 : ℝ)^3479
        have hw : |(1043352449/2000000000 : ℝ)|=(1043352449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s4_2 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676101963/5000000000 : ℝ)*x 0 + (326047713/625000000 : ℝ)*x 1 + (-99652781/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676101963/5000000000 : ℝ)^4503 ≤ (11131909146187/25000000000000 : ℝ)^3479 := by
    have hnat : (2676101963 : ℕ)^4503*25000000000000^3479 ≤ 11131909146187^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676101963 5000000000 11131909146187 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326047713/625000000 : ℝ)^4503 ≤ (43074645551391/100000000000000 : ℝ)^3479 := by
    have hnat : (326047713 : ℕ)^4503*100000000000000^3479 ≤ 43074645551391^3479*625000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326047713 625000000 43074645551391 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99652781/500000000 : ℝ)^4503 ≤ (12397717848227/100000000000000 : ℝ)^3479 := by
    have hnat : (99652781 : ℕ)^4503*100000000000000^3479 ≤ 12397717848227^3479*500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99652781 500000000 12397717848227 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676101963/5000000000 : ℝ), (326047713/625000000 : ℝ), (-99652781/500000000 : ℝ)] ![(11131909146187/25000000000000 : ℝ), (43074645551391/100000000000000 : ℝ), (12397717848227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676101963/5000000000 : ℝ)|^4503 ≤ (11131909146187/25000000000000 : ℝ)^3479
        have hw : |(2676101963/5000000000 : ℝ)|=(2676101963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326047713/625000000 : ℝ)|^4503 ≤ (43074645551391/100000000000000 : ℝ)^3479
        have hw : |(326047713/625000000 : ℝ)|=(326047713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99652781/500000000 : ℝ)|^4503 ≤ (12397717848227/100000000000000 : ℝ)^3479
        have hw : |(-99652781/500000000 : ℝ)|=(99652781/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s4_3 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273941001/10000000000 : ℝ)*x 0 + (1008567821/2500000000 : ℝ)*x 1 + (4525689049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273941001/10000000000 : ℝ)^4503 ≤ (16639395118173/50000000000000 : ℝ)^3479 := by
    have hnat : (4273941001 : ℕ)^4503*50000000000000^3479 ≤ 16639395118173^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273941001 10000000000 16639395118173 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008567821/2500000000 : ℝ)^4503 ≤ (1930220925509/6250000000000 : ℝ)^3479 := by
    have hnat : (1008567821 : ℕ)^4503*6250000000000^3479 ≤ 1930220925509^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008567821 2500000000 1930220925509 6250000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4525689049/10000000000 : ℝ)^4503 ≤ (35837674935251/100000000000000 : ℝ)^3479 := by
    have hnat : (4525689049 : ℕ)^4503*100000000000000^3479 ≤ 35837674935251^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525689049 10000000000 35837674935251 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273941001/10000000000 : ℝ), (1008567821/2500000000 : ℝ), (4525689049/10000000000 : ℝ)] ![(16639395118173/50000000000000 : ℝ), (1930220925509/6250000000000 : ℝ), (35837674935251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273941001/10000000000 : ℝ)|^4503 ≤ (16639395118173/50000000000000 : ℝ)^3479
        have hw : |(4273941001/10000000000 : ℝ)|=(4273941001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008567821/2500000000 : ℝ)|^4503 ≤ (1930220925509/6250000000000 : ℝ)^3479
        have hw : |(1008567821/2500000000 : ℝ)|=(1008567821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4525689049/10000000000 : ℝ)|^4503 ≤ (35837674935251/100000000000000 : ℝ)^3479
        have hw : |(4525689049/10000000000 : ℝ)|=(4525689049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s4_4 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-940678217/5000000000 : ℝ)*x 0 + (521788761/1000000000 : ℝ)*x 1 + (84901953/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (940678217/5000000000 : ℝ)^4503 ≤ (575295204113/5000000000000 : ℝ)^3479 := by
    have hnat : (940678217 : ℕ)^4503*5000000000000^3479 ≤ 575295204113^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940678217 5000000000 575295204113 5000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521788761/1000000000 : ℝ)^4503 ≤ (8617332123783/20000000000000 : ℝ)^3479 := by
    have hnat : (521788761 : ℕ)^4503*20000000000000^3479 ≤ 8617332123783^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521788761 1000000000 8617332123783 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84901953/156250000 : ℝ)^4503 ≤ (45407435284607/100000000000000 : ℝ)^3479 := by
    have hnat : (84901953 : ℕ)^4503*100000000000000^3479 ≤ 45407435284607^3479*156250000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84901953 156250000 45407435284607 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-940678217/5000000000 : ℝ), (521788761/1000000000 : ℝ), (84901953/156250000 : ℝ)] ![(575295204113/5000000000000 : ℝ), (8617332123783/20000000000000 : ℝ), (45407435284607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-940678217/5000000000 : ℝ)|^4503 ≤ (575295204113/5000000000000 : ℝ)^3479
        have hw : |(-940678217/5000000000 : ℝ)|=(940678217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521788761/1000000000 : ℝ)|^4503 ≤ (8617332123783/20000000000000 : ℝ)^3479
        have hw : |(521788761/1000000000 : ℝ)|=(521788761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84901953/156250000 : ℝ)|^4503 ≤ (45407435284607/100000000000000 : ℝ)^3479
        have hw : |(84901953/156250000 : ℝ)|=(84901953/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s4_5 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295030671/10000000000 : ℝ)*x 0 + (-355218701/2000000000 : ℝ)*x 1 + (84901953/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295030671/10000000000 : ℝ)^4503 ≤ (43912951864131/100000000000000 : ℝ)^3479 := by
    have hnat : (5295030671 : ℕ)^4503*100000000000000^3479 ≤ 43912951864131^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295030671 10000000000 43912951864131 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355218701/2000000000 : ℝ)^4503 ≤ (533980641907/5000000000000 : ℝ)^3479 := by
    have hnat : (355218701 : ℕ)^4503*5000000000000^3479 ≤ 533980641907^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355218701 2000000000 533980641907 5000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84901953/156250000 : ℝ)^4503 ≤ (45407435284607/100000000000000 : ℝ)^3479 := by
    have hnat : (84901953 : ℕ)^4503*100000000000000^3479 ≤ 45407435284607^3479*156250000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84901953 156250000 45407435284607 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295030671/10000000000 : ℝ), (-355218701/2000000000 : ℝ), (84901953/156250000 : ℝ)] ![(43912951864131/100000000000000 : ℝ), (533980641907/5000000000000 : ℝ), (45407435284607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295030671/10000000000 : ℝ)|^4503 ≤ (43912951864131/100000000000000 : ℝ)^3479
        have hw : |(5295030671/10000000000 : ℝ)|=(5295030671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-355218701/2000000000 : ℝ)|^4503 ≤ (533980641907/5000000000000 : ℝ)^3479
        have hw : |(-355218701/2000000000 : ℝ)|=(355218701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84901953/156250000 : ℝ)|^4503 ≤ (45407435284607/100000000000000 : ℝ)^3479
        have hw : |(84901953/156250000 : ℝ)|=(84901953/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s4_6 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529503067/1000000000 : ℝ)*x 0 + (84901953/156250000 : ℝ)*x 1 + (-888046753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529503067/1000000000 : ℝ)^4503 ≤ (43912951853397/100000000000000 : ℝ)^3479 := by
    have hnat : (529503067 : ℕ)^4503*100000000000000^3479 ≤ 43912951853397^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529503067 1000000000 43912951853397 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84901953/156250000 : ℝ)^4503 ≤ (45407435284607/100000000000000 : ℝ)^3479 := by
    have hnat : (84901953 : ℕ)^4503*100000000000000^3479 ≤ 45407435284607^3479*156250000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84901953 156250000 45407435284607 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888046753/5000000000 : ℝ)^4503 ≤ (10679612845923/100000000000000 : ℝ)^3479 := by
    have hnat : (888046753 : ℕ)^4503*100000000000000^3479 ≤ 10679612845923^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888046753 5000000000 10679612845923 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529503067/1000000000 : ℝ), (84901953/156250000 : ℝ), (-888046753/5000000000 : ℝ)] ![(43912951853397/100000000000000 : ℝ), (45407435284607/100000000000000 : ℝ), (10679612845923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529503067/1000000000 : ℝ)|^4503 ≤ (43912951853397/100000000000000 : ℝ)^3479
        have hw : |(529503067/1000000000 : ℝ)|=(529503067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84901953/156250000 : ℝ)|^4503 ≤ (45407435284607/100000000000000 : ℝ)^3479
        have hw : |(84901953/156250000 : ℝ)|=(84901953/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-888046753/5000000000 : ℝ)|^4503 ≤ (10679612845923/100000000000000 : ℝ)^3479
        have hw : |(-888046753/5000000000 : ℝ)|=(888046753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s4_7 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2137003167/5000000000 : ℝ)*x 0 + (1130788501/2500000000 : ℝ)*x 1 + (126150833/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137003167/5000000000 : ℝ)^4503 ≤ (16639724341127/50000000000000 : ℝ)^3479 := by
    have hnat : (2137003167 : ℕ)^4503*50000000000000^3479 ≤ 16639724341127^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137003167 5000000000 16639724341127 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130788501/2500000000 : ℝ)^4503 ≤ (17905847068267/50000000000000 : ℝ)^3479 := by
    have hnat : (1130788501 : ℕ)^4503*50000000000000^3479 ≤ 17905847068267^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130788501 2500000000 17905847068267 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126150833/312500000 : ℝ)^4503 ≤ (15454428579731/50000000000000 : ℝ)^3479 := by
    have hnat : (126150833 : ℕ)^4503*50000000000000^3479 ≤ 15454428579731^3479*312500000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126150833 312500000 15454428579731 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2137003167/5000000000 : ℝ), (1130788501/2500000000 : ℝ), (126150833/312500000 : ℝ)] ![(16639724341127/50000000000000 : ℝ), (17905847068267/50000000000000 : ℝ), (15454428579731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2137003167/5000000000 : ℝ)|^4503 ≤ (16639724341127/50000000000000 : ℝ)^3479
        have hw : |(2137003167/5000000000 : ℝ)|=(2137003167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130788501/2500000000 : ℝ)|^4503 ≤ (17905847068267/50000000000000 : ℝ)^3479
        have hw : |(1130788501/2500000000 : ℝ)|=(1130788501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126150833/312500000 : ℝ)|^4503 ≤ (15454428579731/50000000000000 : ℝ)^3479
        have hw : |(126150833/312500000 : ℝ)|=(126150833/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1503_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3889/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1359/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3889/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3889/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3889/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3889/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3889/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3889/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10811/100000 : ℝ) ^ (4501/1024 : ℝ) ≤ (2833478204517641/50000000000000000000 : ℝ) := by
    have hpowers : (10811/100000 : ℝ)^4501 ≤ (2833478204517641/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10811 : ℕ)^4501*50000000000000000000^1024 ≤ 2833478204517641^1024*100000^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10811 100000 2833478204517641 50000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10811/100000 : ℝ)) (X := (2833478204517641/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3889/25000 : ℝ) ^ (4501/1024 : ℝ) ≤ (14026556390175023/50000000000000000000 : ℝ) := by
    have hpowers : (3889/25000 : ℝ)^4501 ≤ (14026556390175023/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3889 : ℕ)^4501*50000000000000000000^1024 ≤ 14026556390175023^1024*25000^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3889 25000 14026556390175023 50000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3889/25000 : ℝ)) (X := (14026556390175023/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002833478204517641/25000000000000000000 : ℝ) ≤ (10000257840895081/10000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (25002833478204517641/25000000000000000000 : ℝ)^1024 ≤ (10000257840895081/10000000000000000 : ℝ)^4501 := by
      have hnat : (25002833478204517641 : ℕ)^1024*10000000000000000^4501 ≤ 10000257840895081^4501*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002833478204517641 25000000000000000000 10000257840895081 10000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000257840895081/10000000000000000 : ℝ)) (X := (25002833478204517641/25000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252107504324336583/6250000000000000000 : ℝ) ≤ (5000383524267297/5000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (6252107504324336583/6250000000000000000 : ℝ)^1024 ≤ (5000383524267297/5000000000000000 : ℝ)^4501 := by
      have hnat : (6252107504324336583 : ℕ)^1024*5000000000000000^4501 ≤ 5000383524267297^4501*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252107504324336583 6250000000000000000 5000383524267297 5000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000383524267297/5000000000000000 : ℝ)) (X := (6252107504324336583/6250000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014026556390175023/25000000000000000000 : ℝ) ≤ (10001276256174107/10000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (25014026556390175023/25000000000000000000 : ℝ)^1024 ≤ (10001276256174107/10000000000000000 : ℝ)^4501 := by
      have hnat : (25014026556390175023 : ℕ)^1024*10000000000000000^4501 ≤ 10001276256174107^4501*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014026556390175023 25000000000000000000 10001276256174107 10000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001276256174107/10000000000000000 : ℝ)) (X := (25014026556390175023/25000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2833478204517641/50000000000000000000 : ℝ) ≤ ((47440213367465609259/47450000000000000000 : ℝ)+2*(509207639513/474500000000000 : ℝ)*(10811/100000 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (47440213367465609259/47450000000000000000 : ℝ)+2*(509207639513/474500000000000 : ℝ)*(10811/100000 : ℝ)=(10000257840895081/10000000000000000 : ℝ) by norm_num, show 1+2*(2833478204517641/50000000000000000000 : ℝ)=(25002833478204517641/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14026556390175023/50000000000000000000 : ℝ)+(2833478204517641/50000000000000000000 : ℝ) ≤ ((47440213367465609259/47450000000000000000 : ℝ)+(509207639513/474500000000000 : ℝ)*((3889/25000 : ℝ)+(10811/100000 : ℝ)))^(4501/1024 : ℝ) := by
    rw [show (47440213367465609259/47450000000000000000 : ℝ)+(509207639513/474500000000000 : ℝ)*((3889/25000 : ℝ)+(10811/100000 : ℝ))=(5000383524267297/5000000000000000 : ℝ) by norm_num, show 1+(14026556390175023/50000000000000000000 : ℝ)+(2833478204517641/50000000000000000000 : ℝ)=(6252107504324336583/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14026556390175023/50000000000000000000 : ℝ) ≤ ((47440213367465609259/47450000000000000000 : ℝ)+2*(509207639513/474500000000000 : ℝ)*(3889/25000 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (47440213367465609259/47450000000000000000 : ℝ)+2*(509207639513/474500000000000 : ℝ)*(3889/25000 : ℝ)=(10001276256174107/10000000000000000 : ℝ) by norm_num, show 1+2*(14026556390175023/50000000000000000000 : ℝ)=(25014026556390175023/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47440213367465609259/47450000000000000000 : ℝ)*(X 1 0+X 2 0)+(509207639513/474500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (10811/100000 : ℝ)) (hi := (3889/25000 : ℝ)) (c := (47440213367465609259/47450000000000000000 : ℝ)) (alpha := (509207639513/474500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47440213367465609259/47450000000000000000 : ℝ)*(X 0 1+X 2 1)+(509207639513/474500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (10811/100000 : ℝ)) (hi := (3889/25000 : ℝ)) (c := (47440213367465609259/47450000000000000000 : ℝ)) (alpha := (509207639513/474500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47440213367465609259/47450000000000000000 : ℝ)*(X 0 2+X 1 2)+(509207639513/474500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (10811/100000 : ℝ)) (hi := (3889/25000 : ℝ)) (c := (47440213367465609259/47450000000000000000 : ℝ)) (alpha := (509207639513/474500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1881327749/10000000000 : ℝ)*X 0 0+(1086971337/2000000000 : ℝ)*X 0 1+(5216763509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676102217/5000000000 : ℝ)*X 1 0+(-498264121/2500000000 : ℝ)*X 1 1+(1043352449/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676101963/5000000000 : ℝ)*X 2 0+(326047713/625000000 : ℝ)*X 2 1+(-99652781/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4273941001/10000000000 : ℝ)*X 0 0+(1008567821/2500000000 : ℝ)*X 0 1+(4525689049/10000000000 : ℝ)*X 0 2+(4273941001/10000000000 : ℝ)*X 1 0+(1008567821/2500000000 : ℝ)*X 1 1+(4525689049/10000000000 : ℝ)*X 1 2+(4273941001/10000000000 : ℝ)*X 2 0+(1008567821/2500000000 : ℝ)*X 2 1+(4525689049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-940678217/5000000000 : ℝ)*X 0 0+(521788761/1000000000 : ℝ)*X 0 1+(84901953/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295030671/10000000000 : ℝ)*X 1 0+(-355218701/2000000000 : ℝ)*X 1 1+(84901953/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529503067/1000000000 : ℝ)*X 2 0+(84901953/156250000 : ℝ)*X 2 1+(-888046753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2137003167/5000000000 : ℝ)*X 0 0+(1130788501/2500000000 : ℝ)*X 0 1+(126150833/312500000 : ℝ)*X 0 2+(2137003167/5000000000 : ℝ)*X 1 0+(1130788501/2500000000 : ℝ)*X 1 1+(126150833/312500000 : ℝ)*X 1 2+(2137003167/5000000000 : ℝ)*X 2 0+(1130788501/2500000000 : ℝ)*X 2 1+(126150833/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9217618855204019084948908647/2372500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2062763469/100000000000000 : ℝ)*(base19) + (351845389/25000000000000 : ℝ)*(base23) + (182739237/100000000000000 : ℝ)*(upper3) + (23569147/20000000000000 : ℝ)*(upper4) + (6233319/800000000000 : ℝ)*(upper5) + (3310080616103437/100000000000000 : ℝ)*(major0) + (3310080616103437/100000000000000 : ℝ)*(major1) + (3310080616103437/100000000000000 : ℝ)*(major2) + (2292594577697133/50000000000000 : ℝ)*(sp0) + (229259871682663/5000000000000 : ℝ)*(sp1) + (4585198089035173/100000000000000 : ℝ)*(sp2) + (1017474167689443/50000000000000 : ℝ)*(sp3) + (5170511231/50000000000000 : ℝ)*(sp4) + (6635452421/50000000000000 : ℝ)*(sp7) + (127185100392733/6250000000000 : ℝ)*(f.failure) + (4585199496416729/100000000000000 : ℝ)*(f.sum) + (17312061630481/23725000000000000000000000000 : ℝ)*base65 + (1187041355002976817/4745000000000000000000000000000000 : ℝ)*base68 + (116742272292976817/4745000000000000000000000000000000 : ℝ)*base70 + (24935139692342976817/4745000000000000000000000000000000 : ℝ)*base72 + (5131817924981/23725000000000000000000000000 : ℝ)*base73 + (34327048736782976817/4745000000000000000000000000000000 : ℝ)*base76 + (32015317221052976817/4745000000000000000000000000000000 : ℝ)*base78 + (81610452308732976817/4745000000000000000000000000000000 : ℝ)*base80 + (64655420323669/23725000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1420669/625000000000000000000 : ℝ)*base89 + (1420669/625000000000000000000 : ℝ)*base91 + (1420669/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (798813642124127303634337023/91250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286829897/20000000000000 : ℝ)*(base19) + (777294963/50000000000000 : ℝ)*(base23) + (36192233/20000000000000 : ℝ)*(upper3) + (55002177/100000000000000 : ℝ)*(lower4) + (180826317/100000000000000 : ℝ)*(upper5) + (1672336245568813/50000000000000 : ℝ)*(major0) + (1672336245568813/50000000000000 : ℝ)*(major1) + (1672336245568813/50000000000000 : ℝ)*(major2) + (5460740821/25000000000000 : ℝ)*(sp1) + (23458373319/100000000000000 : ℝ)*(sp2) + (926623358639397/20000000000000 : ℝ)*(sp4) + (579136689510527/12500000000000 : ℝ)*(sp5) + (231654589011687/5000000000000 : ℝ)*(sp6) + (514056974318547/25000000000000 : ℝ)*(sp7) + (514056974318547/25000000000000 : ℝ)*(f.failure) + (926623358639397/20000000000000 : ℝ)*(f.sum) + (39690057269047/5931250000000000000000000000 : ℝ)*base65 + (7114709270616339567/2372500000000000000000000000000000 : ℝ)*base67 + (1135184614018660433/2372500000000000000000000000000000 : ℝ)*base70 + (5869639344321339567/2372500000000000000000000000000000 : ℝ)*base71 + (3107289220769/11862500000000000000000000000 : ℝ)*base73 + (35935626746811339567/2372500000000000000000000000000000 : ℝ)*base75 + (610289245423660433/2372500000000000000000000000000000 : ℝ)*base78 + (16411385201821339567/2372500000000000000000000000000000 : ℝ)*base79 + (56787926276919/11862500000000000000000000000 : ℝ)*base81 + (24081629/2500000000000000000000 : ℝ)*base90 + (24081629/2500000000000000000000 : ℝ)*base92 + (24081629/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1503_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3889/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1359/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1503_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1503_s5_0 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-376277537/2000000000 : ℝ)*x 0 + (5434456903/10000000000 : ℝ)*x 1 + (2608561869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (376277537/2000000000 : ℝ)^4503 ≤ (5753075730441/50000000000000 : ℝ)^3479 := by
    have hnat : (376277537 : ℕ)^4503*50000000000000^3479 ≤ 5753075730441^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376277537 2000000000 5753075730441 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434456903/10000000000 : ℝ)^4503 ≤ (45415351976071/100000000000000 : ℝ)^3479 := by
    have hnat : (5434456903 : ℕ)^4503*100000000000000^3479 ≤ 45415351976071^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434456903 10000000000 45415351976071 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608561869/5000000000 : ℝ)^4503 ≤ (5384812068267/12500000000000 : ℝ)^3479 := by
    have hnat : (2608561869 : ℕ)^4503*12500000000000^3479 ≤ 5384812068267^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608561869 5000000000 5384812068267 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-376277537/2000000000 : ℝ), (5434456903/10000000000 : ℝ), (2608561869/5000000000 : ℝ)] ![(5753075730441/50000000000000 : ℝ), (45415351976071/100000000000000 : ℝ), (5384812068267/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-376277537/2000000000 : ℝ)|^4503 ≤ (5753075730441/50000000000000 : ℝ)^3479
        have hw : |(-376277537/2000000000 : ℝ)|=(376277537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434456903/10000000000 : ℝ)|^4503 ≤ (45415351976071/100000000000000 : ℝ)^3479
        have hw : |(5434456903/10000000000 : ℝ)|=(5434456903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608561869/5000000000 : ℝ)|^4503 ≤ (5384812068267/12500000000000 : ℝ)^3479
        have hw : |(2608561869/5000000000 : ℝ)|=(2608561869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s5_1 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352099589/10000000000 : ℝ)*x 0 + (-996358441/5000000000 : ℝ)*x 1 + (1304280929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352099589/10000000000 : ℝ)^4503 ≤ (44526513062673/100000000000000 : ℝ)^3479 := by
    have hnat : (5352099589 : ℕ)^4503*100000000000000^3479 ≤ 44526513062673^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352099589 10000000000 44526513062673 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (996358441/5000000000 : ℝ)^4503 ≤ (6197495305541/50000000000000 : ℝ)^3479 := by
    have hnat : (996358441 : ℕ)^4503*50000000000000^3479 ≤ 6197495305541^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996358441 5000000000 6197495305541 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304280929/2500000000 : ℝ)^4503 ≤ (43078496311011/100000000000000 : ℝ)^3479 := by
    have hnat : (1304280929 : ℕ)^4503*100000000000000^3479 ≤ 43078496311011^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304280929 2500000000 43078496311011 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352099589/10000000000 : ℝ), (-996358441/5000000000 : ℝ), (1304280929/2500000000 : ℝ)] ![(44526513062673/100000000000000 : ℝ), (6197495305541/50000000000000 : ℝ), (43078496311011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352099589/10000000000 : ℝ)|^4503 ≤ (44526513062673/100000000000000 : ℝ)^3479
        have hw : |(5352099589/10000000000 : ℝ)|=(5352099589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-996358441/5000000000 : ℝ)|^4503 ≤ (6197495305541/50000000000000 : ℝ)^3479
        have hw : |(-996358441/5000000000 : ℝ)|=(996358441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304280929/2500000000 : ℝ)|^4503 ≤ (43078496311011/100000000000000 : ℝ)^3479
        have hw : |(1304280929/2500000000 : ℝ)|=(1304280929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s5_2 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676049789/5000000000 : ℝ)*x 0 + (652140467/1250000000 : ℝ)*x 1 + (-199271687/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676049789/5000000000 : ℝ)^4503 ≤ (1391453529507/3125000000000 : ℝ)^3479 := by
    have hnat : (2676049789 : ℕ)^4503*3125000000000^3479 ≤ 1391453529507^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676049789 5000000000 1391453529507 3125000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652140467/1250000000 : ℝ)^4503 ≤ (43078496524761/100000000000000 : ℝ)^3479 := by
    have hnat : (652140467 : ℕ)^4503*100000000000000^3479 ≤ 43078496524761^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652140467 1250000000 43078496524761 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199271687/1000000000 : ℝ)^4503 ≤ (1239499051447/10000000000000 : ℝ)^3479 := by
    have hnat : (199271687 : ℕ)^4503*10000000000000^3479 ≤ 1239499051447^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199271687 1000000000 1239499051447 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676049789/5000000000 : ℝ), (652140467/1250000000 : ℝ), (-199271687/1000000000 : ℝ)] ![(1391453529507/3125000000000 : ℝ), (43078496524761/100000000000000 : ℝ), (1239499051447/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676049789/5000000000 : ℝ)|^4503 ≤ (1391453529507/3125000000000 : ℝ)^3479
        have hw : |(2676049789/5000000000 : ℝ)|=(2676049789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652140467/1250000000 : ℝ)|^4503 ≤ (43078496524761/100000000000000 : ℝ)^3479
        have hw : |(652140467/1250000000 : ℝ)|=(652140467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199271687/1000000000 : ℝ)|^4503 ≤ (1239499051447/10000000000000 : ℝ)^3479
        have hw : |(-199271687/1000000000 : ℝ)|=(199271687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s5_3 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273977189/10000000000 : ℝ)*x 0 + (16140511/40000000 : ℝ)*x 1 + (2262412721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273977189/10000000000 : ℝ)^4503 ≤ (16639577474843/50000000000000 : ℝ)^3479 := by
    have hnat : (4273977189 : ℕ)^4503*50000000000000^3479 ≤ 16639577474843^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273977189 10000000000 16639577474843 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16140511/40000000 : ℝ)^4503 ≤ (241343917157/781250000000 : ℝ)^3479 := by
    have hnat : (16140511 : ℕ)^4503*781250000000^3479 ≤ 241343917157^3479*40000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16140511 40000000 241343917157 781250000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262412721/5000000000 : ℝ)^4503 ≤ (716576472897/2000000000000 : ℝ)^3479 := by
    have hnat : (2262412721 : ℕ)^4503*2000000000000^3479 ≤ 716576472897^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262412721 5000000000 716576472897 2000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273977189/10000000000 : ℝ), (16140511/40000000 : ℝ), (2262412721/5000000000 : ℝ)] ![(16639577474843/50000000000000 : ℝ), (241343917157/781250000000 : ℝ), (716576472897/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273977189/10000000000 : ℝ)|^4503 ≤ (16639577474843/50000000000000 : ℝ)^3479
        have hw : |(4273977189/10000000000 : ℝ)|=(4273977189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16140511/40000000 : ℝ)|^4503 ≤ (241343917157/781250000000 : ℝ)^3479
        have hw : |(16140511/40000000 : ℝ)|=(16140511/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262412721/5000000000 : ℝ)|^4503 ≤ (716576472897/2000000000000 : ℝ)^3479
        have hw : |(2262412721/5000000000 : ℝ)|=(2262412721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s5_4 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7525669/40000000 : ℝ)*x 0 + (5218240043/10000000000 : ℝ)*x 1 + (5433332223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7525669/40000000 : ℝ)^4503 ≤ (1438298186809/12500000000000 : ℝ)^3479 := by
    have hnat : (7525669 : ℕ)^4503*12500000000000^3479 ≤ 1438298186809^3479*40000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7525669 40000000 1438298186809 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218240043/10000000000 : ℝ)^4503 ≤ (5386303431653/12500000000000 : ℝ)^3479 := by
    have hnat : (5218240043 : ℕ)^4503*12500000000000^3479 ≤ 5386303431653^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218240043 10000000000 5386303431653 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433332223/10000000000 : ℝ)^4503 ≤ (22701593520467/50000000000000 : ℝ)^3479 := by
    have hnat : (5433332223 : ℕ)^4503*50000000000000^3479 ≤ 22701593520467^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433332223 10000000000 22701593520467 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7525669/40000000 : ℝ), (5218240043/10000000000 : ℝ), (5433332223/10000000000 : ℝ)] ![(1438298186809/12500000000000 : ℝ), (5386303431653/12500000000000 : ℝ), (22701593520467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7525669/40000000 : ℝ)|^4503 ≤ (1438298186809/12500000000000 : ℝ)^3479
        have hw : |(-7525669/40000000 : ℝ)|=(7525669/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218240043/10000000000 : ℝ)|^4503 ≤ (5386303431653/12500000000000 : ℝ)^3479
        have hw : |(5218240043/10000000000 : ℝ)|=(5218240043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433332223/10000000000 : ℝ)|^4503 ≤ (22701593520467/50000000000000 : ℝ)^3479
        have hw : |(5433332223/10000000000 : ℝ)|=(5433332223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s5_5 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529512581/1000000000 : ℝ)*x 0 + (-888254683/5000000000 : ℝ)*x 1 + (42447901/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529512581/1000000000 : ℝ)^4503 ≤ (21956986556279/50000000000000 : ℝ)^3479 := by
    have hnat : (529512581 : ℕ)^4503*50000000000000^3479 ≤ 21956986556279^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529512581 1000000000 21956986556279 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (888254683/5000000000 : ℝ)^4503 ≤ (10682849522569/100000000000000 : ℝ)^3479 := by
    have hnat : (888254683 : ℕ)^4503*100000000000000^3479 ≤ 10682849522569^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888254683 5000000000 10682849522569 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42447901/78125000 : ℝ)^4503 ≤ (45403177360593/100000000000000 : ℝ)^3479 := by
    have hnat : (42447901 : ℕ)^4503*100000000000000^3479 ≤ 45403177360593^3479*78125000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42447901 78125000 45403177360593 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529512581/1000000000 : ℝ), (-888254683/5000000000 : ℝ), (42447901/78125000 : ℝ)] ![(21956986556279/50000000000000 : ℝ), (10682849522569/100000000000000 : ℝ), (45403177360593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529512581/1000000000 : ℝ)|^4503 ≤ (21956986556279/50000000000000 : ℝ)^3479
        have hw : |(529512581/1000000000 : ℝ)|=(529512581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-888254683/5000000000 : ℝ)|^4503 ≤ (10682849522569/100000000000000 : ℝ)^3479
        have hw : |(-888254683/5000000000 : ℝ)|=(888254683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42447901/78125000 : ℝ)|^4503 ≤ (45403177360593/100000000000000 : ℝ)^3479
        have hw : |(42447901/78125000 : ℝ)|=(42447901/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s5_6 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529512553/1000000000 : ℝ)*x 0 + (67916647/125000000 : ℝ)*x 1 + (-35530183/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529512553/1000000000 : ℝ)^4503 ≤ (5489246263369/12500000000000 : ℝ)^3479 := by
    have hnat : (529512553 : ℕ)^4503*12500000000000^3479 ≤ 5489246263369^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529512553 1000000000 5489246263369 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67916647/125000000 : ℝ)^4503 ≤ (9080636406623/20000000000000 : ℝ)^3479 := by
    have hnat : (67916647 : ℕ)^4503*20000000000000^3479 ≤ 9080636406623^3479*125000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67916647 125000000 9080636406623 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35530183/200000000 : ℝ)^4503 ≤ (2670711960341/25000000000000 : ℝ)^3479 := by
    have hnat : (35530183 : ℕ)^4503*25000000000000^3479 ≤ 2670711960341^3479*200000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35530183 200000000 2670711960341 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529512553/1000000000 : ℝ), (67916647/125000000 : ℝ), (-35530183/200000000 : ℝ)] ![(5489246263369/12500000000000 : ℝ), (9080636406623/20000000000000 : ℝ), (2670711960341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529512553/1000000000 : ℝ)|^4503 ≤ (5489246263369/12500000000000 : ℝ)^3479
        have hw : |(529512553/1000000000 : ℝ)|=(529512553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67916647/125000000 : ℝ)|^4503 ≤ (9080636406623/20000000000000 : ℝ)^3479
        have hw : |(67916647/125000000 : ℝ)|=(67916647/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35530183/200000000 : ℝ)|^4503 ≤ (2670711960341/25000000000000 : ℝ)^3479
        have hw : |(-35530183/200000000 : ℝ)|=(35530183/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s5_7 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4274043103/10000000000 : ℝ)*x 0 + (4522307829/10000000000 : ℝ)*x 1 + (20188321/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274043103/10000000000 : ℝ)^4503 ≤ (33279819252759/100000000000000 : ℝ)^3479 := by
    have hnat : (4274043103 : ℕ)^4503*100000000000000^3479 ≤ 33279819252759^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274043103 10000000000 33279819252759 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522307829/10000000000 : ℝ)^4503 ≤ (4475377866969/12500000000000 : ℝ)^3479 := by
    have hnat : (4522307829 : ℕ)^4503*12500000000000^3479 ≤ 4475377866969^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522307829 10000000000 4475377866969 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20188321/50000000 : ℝ)^4503 ≤ (309171577933/1000000000000 : ℝ)^3479 := by
    have hnat : (20188321 : ℕ)^4503*1000000000000^3479 ≤ 309171577933^3479*50000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20188321 50000000 309171577933 1000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274043103/10000000000 : ℝ), (4522307829/10000000000 : ℝ), (20188321/50000000 : ℝ)] ![(33279819252759/100000000000000 : ℝ), (4475377866969/12500000000000 : ℝ), (309171577933/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274043103/10000000000 : ℝ)|^4503 ≤ (33279819252759/100000000000000 : ℝ)^3479
        have hw : |(4274043103/10000000000 : ℝ)|=(4274043103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522307829/10000000000 : ℝ)|^4503 ≤ (4475377866969/12500000000000 : ℝ)^3479
        have hw : |(4522307829/10000000000 : ℝ)|=(4522307829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20188321/50000000 : ℝ)|^4503 ≤ (309171577933/1000000000000 : ℝ)^3479
        have hw : |(20188321/50000000 : ℝ)|=(20188321/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1503_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1359/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (68/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1359/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1359/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1359/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1359/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1359/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1359/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1359/12500 : ℝ) ^ (4501/1024 : ℝ) ≤ (1161771254822167/20000000000000000000 : ℝ) := by
    have hpowers : (1359/12500 : ℝ)^4501 ≤ (1161771254822167/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1359 : ℕ)^4501*20000000000000000000^1024 ≤ 1161771254822167^1024*12500^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1359 12500 1161771254822167 20000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1359/12500 : ℝ)) (X := (1161771254822167/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4501/1024 : ℝ) ≤ (27533706523243401/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4501 ≤ (27533706523243401/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4501*100000000000000000000^1024 ≤ 27533706523243401^1024*10000^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 27533706523243401 100000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (27533706523243401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001161771254822167/10000000000000000000 : ℝ) ≤ (2500066074227123/2500000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (10001161771254822167/10000000000000000000 : ℝ)^1024 ≤ (2500066074227123/2500000000000000 : ℝ)^4501 := by
      have hnat : (10001161771254822167 : ℕ)^1024*2500000000000000^4501 ≤ 2500066074227123^4501*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001161771254822167 10000000000000000000 2500066074227123 2500000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500066074227123/2500000000000000 : ℝ)) (X := (10001161771254822167/10000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008335640699338559/25000000000000000000 : ℝ) ≤ (2500189615574863/2500000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (25008335640699338559/25000000000000000000 : ℝ)^1024 ≤ (2500189615574863/2500000000000000 : ℝ)^4501 := by
      have hnat : (25008335640699338559 : ℕ)^1024*2500000000000000^4501 ≤ 2500189615574863^4501*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008335640699338559 25000000000000000000 2500189615574863 2500000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500189615574863/2500000000000000 : ℝ)) (X := (25008335640699338559/25000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027533706523243401/50000000000000000000 : ℝ) ≤ (2500313156922603/2500000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (50027533706523243401/50000000000000000000 : ℝ)^1024 ≤ (2500313156922603/2500000000000000 : ℝ)^4501 := by
      have hnat : (50027533706523243401 : ℕ)^1024*2500000000000000^4501 ≤ 2500313156922603^4501*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027533706523243401 50000000000000000000 2500313156922603 2500000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500313156922603/2500000000000000 : ℝ)) (X := (50027533706523243401/50000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1161771254822167/20000000000000000000 : ℝ) ≤ ((5771309423857797727/5772500000000000000 : ℝ)+2*(6177067387/5772500000000 : ℝ)*(1359/12500 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (5771309423857797727/5772500000000000000 : ℝ)+2*(6177067387/5772500000000 : ℝ)*(1359/12500 : ℝ)=(2500066074227123/2500000000000000 : ℝ) by norm_num, show 1+2*(1161771254822167/20000000000000000000 : ℝ)=(10001161771254822167/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27533706523243401/100000000000000000000 : ℝ)+(1161771254822167/20000000000000000000 : ℝ) ≤ ((5771309423857797727/5772500000000000000 : ℝ)+(6177067387/5772500000000 : ℝ)*((1549/10000 : ℝ)+(1359/12500 : ℝ)))^(4501/1024 : ℝ) := by
    rw [show (5771309423857797727/5772500000000000000 : ℝ)+(6177067387/5772500000000 : ℝ)*((1549/10000 : ℝ)+(1359/12500 : ℝ))=(2500189615574863/2500000000000000 : ℝ) by norm_num, show 1+(27533706523243401/100000000000000000000 : ℝ)+(1161771254822167/20000000000000000000 : ℝ)=(25008335640699338559/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27533706523243401/100000000000000000000 : ℝ) ≤ ((5771309423857797727/5772500000000000000 : ℝ)+2*(6177067387/5772500000000 : ℝ)*(1549/10000 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (5771309423857797727/5772500000000000000 : ℝ)+2*(6177067387/5772500000000 : ℝ)*(1549/10000 : ℝ)=(2500313156922603/2500000000000000 : ℝ) by norm_num, show 1+2*(27533706523243401/100000000000000000000 : ℝ)=(50027533706523243401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5771309423857797727/5772500000000000000 : ℝ)*(X 1 0+X 2 0)+(6177067387/5772500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (1359/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (5771309423857797727/5772500000000000000 : ℝ)) (alpha := (6177067387/5772500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5771309423857797727/5772500000000000000 : ℝ)*(X 0 1+X 2 1)+(6177067387/5772500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (1359/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (5771309423857797727/5772500000000000000 : ℝ)) (alpha := (6177067387/5772500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5771309423857797727/5772500000000000000 : ℝ)*(X 0 2+X 1 2)+(6177067387/5772500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (1359/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (5771309423857797727/5772500000000000000 : ℝ)) (alpha := (6177067387/5772500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-376277537/2000000000 : ℝ)*X 0 0+(5434456903/10000000000 : ℝ)*X 0 1+(2608561869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352099589/10000000000 : ℝ)*X 1 0+(-996358441/5000000000 : ℝ)*X 1 1+(1304280929/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676049789/5000000000 : ℝ)*X 2 0+(652140467/1250000000 : ℝ)*X 2 1+(-199271687/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4273977189/10000000000 : ℝ)*X 0 0+(16140511/40000000 : ℝ)*X 0 1+(2262412721/5000000000 : ℝ)*X 0 2+(4273977189/10000000000 : ℝ)*X 1 0+(16140511/40000000 : ℝ)*X 1 1+(2262412721/5000000000 : ℝ)*X 1 2+(4273977189/10000000000 : ℝ)*X 2 0+(16140511/40000000 : ℝ)*X 2 1+(2262412721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-7525669/40000000 : ℝ)*X 0 0+(5218240043/10000000000 : ℝ)*X 0 1+(5433332223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529512581/1000000000 : ℝ)*X 1 0+(-888254683/5000000000 : ℝ)*X 1 1+(42447901/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529512553/1000000000 : ℝ)*X 2 0+(67916647/125000000 : ℝ)*X 2 1+(-35530183/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4274043103/10000000000 : ℝ)*X 0 0+(4522307829/10000000000 : ℝ)*X 0 1+(20188321/50000000 : ℝ)*X 0 2+(4274043103/10000000000 : ℝ)*X 1 0+(4522307829/10000000000 : ℝ)*X 1 1+(20188321/50000000 : ℝ)*X 1 2+(4274043103/10000000000 : ℝ)*X 2 0+(4522307829/10000000000 : ℝ)*X 2 1+(20188321/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (274750573949536313575063797/72156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (672009863/100000000000000 : ℝ)*(base19) + (617150949/100000000000000 : ℝ)*(base23) + (24299661/100000000000000 : ℝ)*(lower2) + (17629839/20000000000000 : ℝ)*(upper3) + (64714919/100000000000000 : ℝ)*(upper5) + (1660834280820637/50000000000000 : ℝ)*(major0) + (1660834280820637/50000000000000 : ℝ)*(major1) + (1660834280820637/50000000000000 : ℝ)*(major2) + (17973597915539/390625000000 : ℝ)*(sp0) + (18405002860229/400000000000 : ℝ)*(sp1) + (1150312692479041/25000000000000 : ℝ)*(sp2) + (510520173293627/25000000000000 : ℝ)*(sp3) + (10320689129/100000000000000 : ℝ)*(sp4) + (4916117027/100000000000000 : ℝ)*(sp7) + (408417121858307/20000000000000 : ℝ)*(f.failure) + (4601251387067113/100000000000000 : ℝ)*(f.sum) + (83425303123/2309000000000000000000000000 : ℝ)*base66 + (372082519609957901/288625000000000000000000000000000 : ℝ)*base68 + (1457755966812082901/288625000000000000000000000000000 : ℝ)*base70 + (506716142153582901/288625000000000000000000000000000 : ℝ)*base72 + (8006164555457/2309000000000000000000000000 : ℝ)*base73 + (44721000770707901/288625000000000000000000000000000 : ℝ)*base76 + (1258096070088332901/288625000000000000000000000000000 : ℝ)*base78 + (1568674522271917099/288625000000000000000000000000000 : ℝ)*base79 + (21733453769/11545000000000000000000000 : ℝ)*base82 + (1403949/2000000000000000000000 : ℝ)*base90 + (1403949/2000000000000000000000 : ℝ)*base92 + (1403949/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (386192205734527817837454369/144312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103091471/50000000000000 : ℝ)*(base19) + (248686629/100000000000000 : ℝ)*(base23) + (16594187/20000000000000 : ℝ)*(lower1) + (12763049/10000000000000 : ℝ)*(upper2) + (139996669/100000000000000 : ℝ)*(upper5) + (1678142882408549/50000000000000 : ℝ)*(major0) + (1678142882408549/50000000000000 : ℝ)*(major1) + (1678142882408549/50000000000000 : ℝ)*(major2) + (9364058323/50000000000000 : ℝ)*(sp0) + (2198672259/50000000000000 : ℝ)*(sp2) + (1162296310218129/25000000000000 : ℝ)*(sp4) + (232460188140311/5000000000000 : ℝ)*(sp5) + (929839864591603/20000000000000 : ℝ)*(sp6) + (515841867860567/25000000000000 : ℝ)*(sp7) + (515841867860567/25000000000000 : ℝ)*(f.failure) + (2324601984494581/50000000000000 : ℝ)*(f.sum) + (4071570700819/1154500000000000000000000000 : ℝ)*base66 + (1811487167504681877/288625000000000000000000000000000 : ℝ)*base68 + (62944682637568123/288625000000000000000000000000000 : ℝ)*base69 + (457672586348931877/288625000000000000000000000000000 : ℝ)*base72 + (741729733653/115450000000000000000000000 : ℝ)*base74 + (1848282254899431877/288625000000000000000000000000000 : ℝ)*base76 + (2161281116047181877/288625000000000000000000000000000 : ℝ)*base78 + (1080515093533068123/288625000000000000000000000000000 : ℝ)*base79 + (1311828035401/1154500000000000000000000000 : ℝ)*base82 + (19536231/2500000000000000000000 : ℝ)*base89 + (19536231/2500000000000000000000 : ℝ)*base91 + (19536231/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1503_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1359/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1503_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1503_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5187/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1503_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1503_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1503_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5187/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1503_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
