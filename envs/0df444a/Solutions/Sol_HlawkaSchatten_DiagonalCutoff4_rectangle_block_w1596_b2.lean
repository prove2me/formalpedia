-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1596_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:50.463008+00:00
-- url     : https://prove2.me/submissions/5f1472c8-61f8-45f0-a15a-c6fb0307dfcd

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
theorem support_rectangle_w1596_s6_0 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-348034343/2000000000 : ℝ)*x 0 + (170742181/312500000 : ℝ)*x 1 + (323710851/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (348034343/2000000000 : ℝ)^4703 ≤ (213919887767/2000000000000 : ℝ)^3679 := by
    have hnat : (348034343 : ℕ)^4703*2000000000000^3679 ≤ 213919887767^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348034343 2000000000 213919887767 2000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170742181/312500000 : ℝ)^4703 ≤ (11544228632537/25000000000000 : ℝ)^3679 := by
    have hnat : (170742181 : ℕ)^4703*25000000000000^3679 ≤ 11544228632537^3679*312500000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170742181 312500000 11544228632537 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323710851/625000000 : ℝ)^4703 ≤ (8625418214263/20000000000000 : ℝ)^3679 := by
    have hnat : (323710851 : ℕ)^4703*20000000000000^3679 ≤ 8625418214263^3679*625000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323710851 625000000 8625418214263 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-348034343/2000000000 : ℝ), (170742181/312500000 : ℝ), (323710851/625000000 : ℝ)] ![(213919887767/2000000000000 : ℝ), (11544228632537/25000000000000 : ℝ), (8625418214263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-348034343/2000000000 : ℝ)|^4703 ≤ (213919887767/2000000000000 : ℝ)^3679
        have hw : |(-348034343/2000000000 : ℝ)|=(348034343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170742181/312500000 : ℝ)|^4703 ≤ (11544228632537/25000000000000 : ℝ)^3679
        have hw : |(170742181/312500000 : ℝ)|=(170742181/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323710851/625000000 : ℝ)|^4703 ≤ (8625418214263/20000000000000 : ℝ)^3679
        have hw : |(323710851/625000000 : ℝ)|=(323710851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s6_1 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214220383/400000000 : ℝ)*x 0 + (-943451201/5000000000 : ℝ)*x 1 + (323710851/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214220383/400000000 : ℝ)^4703 ≤ (11252685253219/25000000000000 : ℝ)^3679 := by
    have hnat : (214220383 : ℕ)^4703*25000000000000^3679 ≤ 11252685253219^3679*400000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214220383 400000000 11252685253219 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943451201/5000000000 : ℝ)^4703 ≤ (1186216791353/10000000000000 : ℝ)^3679 := by
    have hnat : (943451201 : ℕ)^4703*10000000000000^3679 ≤ 1186216791353^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943451201 5000000000 1186216791353 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323710851/625000000 : ℝ)^4703 ≤ (8625418214263/20000000000000 : ℝ)^3679 := by
    have hnat : (323710851 : ℕ)^4703*20000000000000^3679 ≤ 8625418214263^3679*625000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323710851 625000000 8625418214263 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214220383/400000000 : ℝ), (-943451201/5000000000 : ℝ), (323710851/625000000 : ℝ)] ![(11252685253219/25000000000000 : ℝ), (1186216791353/10000000000000 : ℝ), (8625418214263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214220383/400000000 : ℝ)|^4703 ≤ (11252685253219/25000000000000 : ℝ)^3679
        have hw : |(214220383/400000000 : ℝ)|=(214220383/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-943451201/5000000000 : ℝ)|^4703 ≤ (1186216791353/10000000000000 : ℝ)^3679
        have hw : |(-943451201/5000000000 : ℝ)|=(943451201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323710851/625000000 : ℝ)|^4703 ≤ (8625418214263/20000000000000 : ℝ)^3679
        have hw : |(323710851/625000000 : ℝ)|=(323710851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s6_2 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355509547/10000000000 : ℝ)*x 0 + (517937363/1000000000 : ℝ)*x 1 + (-1886902419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355509547/10000000000 : ℝ)^4703 ≤ (45010740712047/100000000000000 : ℝ)^3679 := by
    have hnat : (5355509547 : ℕ)^4703*100000000000000^3679 ≤ 45010740712047^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355509547 10000000000 45010740712047 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517937363/1000000000 : ℝ)^4703 ≤ (8625418244067/20000000000000 : ℝ)^3679 := by
    have hnat : (517937363 : ℕ)^4703*20000000000000^3679 ≤ 8625418244067^3679*1000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517937363 1000000000 8625418244067 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1886902419/10000000000 : ℝ)^4703 ≤ (2965542012537/25000000000000 : ℝ)^3679 := by
    have hnat : (1886902419 : ℕ)^4703*25000000000000^3679 ≤ 2965542012537^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886902419 10000000000 2965542012537 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355509547/10000000000 : ℝ), (517937363/1000000000 : ℝ), (-1886902419/10000000000 : ℝ)] ![(45010740712047/100000000000000 : ℝ), (8625418244067/20000000000000 : ℝ), (2965542012537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355509547/10000000000 : ℝ)|^4703 ≤ (45010740712047/100000000000000 : ℝ)^3679
        have hw : |(5355509547/10000000000 : ℝ)|=(5355509547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517937363/1000000000 : ℝ)|^4703 ≤ (8625418244067/20000000000000 : ℝ)^3679
        have hw : |(517937363/1000000000 : ℝ)|=(517937363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1886902419/10000000000 : ℝ)|^4703 ≤ (2965542012537/25000000000000 : ℝ)^3679
        have hw : |(-1886902419/10000000000 : ℝ)|=(1886902419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s6_3 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2112121527/5000000000 : ℝ)*x 0 + (1946113989/5000000000 : ℝ)*x 1 + (4578172583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112121527/5000000000 : ℝ)^4703 ≤ (16616944127699/50000000000000 : ℝ)^3679 := by
    have hnat : (2112121527 : ℕ)^4703*50000000000000^3679 ≤ 16616944127699^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112121527 5000000000 16616944127699 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1946113989/5000000000 : ℝ)^4703 ≤ (29931982943929/100000000000000 : ℝ)^3679 := by
    have hnat : (1946113989 : ℕ)^4703*100000000000000^3679 ≤ 29931982943929^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946113989 5000000000 29931982943929 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4578172583/10000000000 : ℝ)^4703 ≤ (7366825755773/20000000000000 : ℝ)^3679 := by
    have hnat : (4578172583 : ℕ)^4703*20000000000000^3679 ≤ 7366825755773^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578172583 10000000000 7366825755773 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2112121527/5000000000 : ℝ), (1946113989/5000000000 : ℝ), (4578172583/10000000000 : ℝ)] ![(16616944127699/50000000000000 : ℝ), (29931982943929/100000000000000 : ℝ), (7366825755773/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2112121527/5000000000 : ℝ)|^4703 ≤ (16616944127699/50000000000000 : ℝ)^3679
        have hw : |(2112121527/5000000000 : ℝ)|=(2112121527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1946113989/5000000000 : ℝ)|^4703 ≤ (29931982943929/100000000000000 : ℝ)^3679
        have hw : |(1946113989/5000000000 : ℝ)|=(1946113989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4578172583/10000000000 : ℝ)|^4703 ≤ (7366825755773/20000000000000 : ℝ)^3679
        have hw : |(4578172583/10000000000 : ℝ)|=(4578172583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s6_4 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-108765273/625000000 : ℝ)*x 0 + (5181473497/10000000000 : ℝ)*x 1 + (5461627851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108765273/625000000 : ℝ)^4703 ≤ (10696565249289/100000000000000 : ℝ)^3679 := by
    have hnat : (108765273 : ℕ)^4703*100000000000000^3679 ≤ 10696565249289^3679*625000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108765273 625000000 10696565249289 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181473497/10000000000 : ℝ)^4703 ≤ (10787361036921/25000000000000 : ℝ)^3679 := by
    have hnat : (5181473497 : ℕ)^4703*25000000000000^3679 ≤ 10787361036921^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181473497 10000000000 10787361036921 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461627851/10000000000 : ℝ)^4703 ≤ (46153990597323/100000000000000 : ℝ)^3679 := by
    have hnat : (5461627851 : ℕ)^4703*100000000000000^3679 ≤ 46153990597323^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461627851 10000000000 46153990597323 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108765273/625000000 : ℝ), (5181473497/10000000000 : ℝ), (5461627851/10000000000 : ℝ)] ![(10696565249289/100000000000000 : ℝ), (10787361036921/25000000000000 : ℝ), (46153990597323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108765273/625000000 : ℝ)|^4703 ≤ (10696565249289/100000000000000 : ℝ)^3679
        have hw : |(-108765273/625000000 : ℝ)|=(108765273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181473497/10000000000 : ℝ)|^4703 ≤ (10787361036921/25000000000000 : ℝ)^3679
        have hw : |(5181473497/10000000000 : ℝ)|=(5181473497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461627851/10000000000 : ℝ)|^4703 ≤ (46153990597323/100000000000000 : ℝ)^3679
        have hw : |(5461627851/10000000000 : ℝ)|=(5461627851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s6_5 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2112209027/5000000000 : ℝ)*x 0 + (2286553633/5000000000 : ℝ)*x 1 + (3897346603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112209027/5000000000 : ℝ)^4703 ≤ (2077228017313/6250000000000 : ℝ)^3679 := by
    have hnat : (2112209027 : ℕ)^4703*6250000000000^3679 ≤ 2077228017313^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112209027 5000000000 2077228017313 6250000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2286553633/5000000000 : ℝ)^4703 ≤ (3678204012087/10000000000000 : ℝ)^3679 := by
    have hnat : (2286553633 : ℕ)^4703*10000000000000^3679 ≤ 3678204012087^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286553633 5000000000 3678204012087 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3897346603/10000000000 : ℝ)^4703 ≤ (29982311581619/100000000000000 : ℝ)^3679 := by
    have hnat : (3897346603 : ℕ)^4703*100000000000000^3679 ≤ 29982311581619^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3897346603 10000000000 29982311581619 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2112209027/5000000000 : ℝ), (2286553633/5000000000 : ℝ), (3897346603/10000000000 : ℝ)] ![(2077228017313/6250000000000 : ℝ), (3678204012087/10000000000000 : ℝ), (29982311581619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2112209027/5000000000 : ℝ)|^4703 ≤ (2077228017313/6250000000000 : ℝ)^3679
        have hw : |(2112209027/5000000000 : ℝ)|=(2112209027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2286553633/5000000000 : ℝ)|^4703 ≤ (3678204012087/10000000000000 : ℝ)^3679
        have hw : |(2286553633/5000000000 : ℝ)|=(2286553633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3897346603/10000000000 : ℝ)|^4703 ≤ (29982311581619/100000000000000 : ℝ)^3679
        have hw : |(3897346603/10000000000 : ℝ)|=(3897346603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1596_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (517/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4091/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10339/100000 : ℝ) ^ (4699/1024 : ℝ) ≤ (3003121396156921/100000000000000000000 : ℝ) := by
    have hpowers : (10339/100000 : ℝ)^4699 ≤ (3003121396156921/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10339 : ℕ)^4699*100000000000000000000^1024 ≤ 3003121396156921^1024*100000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10339 100000 3003121396156921 100000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10339/100000 : ℝ)) (X := (3003121396156921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4091/25000 : ℝ) ^ (4699/1024 : ℝ) ≤ (4939388458165287/20000000000000000000 : ℝ) := by
    have hpowers : (4091/25000 : ℝ)^4699 ≤ (4939388458165287/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4091 : ℕ)^4699*20000000000000000000^1024 ≤ 4939388458165287^1024*25000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4091 25000 4939388458165287 20000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4091/25000 : ℝ)) (X := (4939388458165287/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50003003121396156921/50000000000000000000 : ℝ) ≤ (10000130884191767/10000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (50003003121396156921/50000000000000000000 : ℝ)^1024 ≤ (10000130884191767/10000000000000000 : ℝ)^4699 := by
      have hnat : (50003003121396156921 : ℕ)^1024*10000000000000000^4699 ≤ 10000130884191767^4699*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003003121396156921 50000000000000000000 10000130884191767 10000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000130884191767/10000000000000000 : ℝ)) (X := (50003003121396156921/50000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006925015921745839/25000000000000000000 : ℝ) ≤ (10000603570829561/10000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (25006925015921745839/25000000000000000000 : ℝ)^1024 ≤ (10000603570829561/10000000000000000 : ℝ)^4699 := by
      have hnat : (25006925015921745839 : ℕ)^1024*10000000000000000^4699 ≤ 10000603570829561^4699*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006925015921745839 25000000000000000000 10000603570829561 10000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000603570829561/10000000000000000 : ℝ)) (X := (25006925015921745839/25000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004939388458165287/10000000000000000000 : ℝ) ≤ (2000215251493471/2000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (10004939388458165287/10000000000000000000 : ℝ)^1024 ≤ (2000215251493471/2000000000000000 : ℝ)^4699 := by
      have hnat : (10004939388458165287 : ℕ)^1024*2000000000000000^4699 ≤ 2000215251493471^4699*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004939388458165287 10000000000000000000 2000215251493471 2000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000215251493471/2000000000000000 : ℝ)) (X := (10004939388458165287/10000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3003121396156921/100000000000000000000 : ℝ) ≤ ((60241014362959091843/60250000000000000000 : ℝ)+2*(236343318897/301250000000000 : ℝ)*(10339/100000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (60241014362959091843/60250000000000000000 : ℝ)+2*(236343318897/301250000000000 : ℝ)*(10339/100000 : ℝ)=(10000130884191767/10000000000000000 : ℝ) by norm_num, show 1+2*(3003121396156921/100000000000000000000 : ℝ)=(50003003121396156921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4939388458165287/20000000000000000000 : ℝ)+(3003121396156921/100000000000000000000 : ℝ) ≤ ((60241014362959091843/60250000000000000000 : ℝ)+(236343318897/301250000000000 : ℝ)*((4091/25000 : ℝ)+(10339/100000 : ℝ)))^(4699/1024 : ℝ) := by
    rw [show (60241014362959091843/60250000000000000000 : ℝ)+(236343318897/301250000000000 : ℝ)*((4091/25000 : ℝ)+(10339/100000 : ℝ))=(10000603570829561/10000000000000000 : ℝ) by norm_num, show 1+(4939388458165287/20000000000000000000 : ℝ)+(3003121396156921/100000000000000000000 : ℝ)=(25006925015921745839/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4939388458165287/20000000000000000000 : ℝ) ≤ ((60241014362959091843/60250000000000000000 : ℝ)+2*(236343318897/301250000000000 : ℝ)*(4091/25000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (60241014362959091843/60250000000000000000 : ℝ)+2*(236343318897/301250000000000 : ℝ)*(4091/25000 : ℝ)=(2000215251493471/2000000000000000 : ℝ) by norm_num, show 1+2*(4939388458165287/20000000000000000000 : ℝ)=(10004939388458165287/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60241014362959091843/60250000000000000000 : ℝ)*(X 1 0+X 2 0)+(236343318897/301250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (10339/100000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (60241014362959091843/60250000000000000000 : ℝ)) (alpha := (236343318897/301250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60241014362959091843/60250000000000000000 : ℝ)*(X 0 1+X 2 1)+(236343318897/301250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (10339/100000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (60241014362959091843/60250000000000000000 : ℝ)) (alpha := (236343318897/301250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60241014362959091843/60250000000000000000 : ℝ)*(X 0 2+X 1 2)+(236343318897/301250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (10339/100000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (60241014362959091843/60250000000000000000 : ℝ)) (alpha := (236343318897/301250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-348034343/2000000000 : ℝ)*X 0 0+(170742181/312500000 : ℝ)*X 0 1+(323710851/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214220383/400000000 : ℝ)*X 1 0+(-943451201/5000000000 : ℝ)*X 1 1+(323710851/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355509547/10000000000 : ℝ)*X 2 0+(517937363/1000000000 : ℝ)*X 2 1+(-1886902419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2112121527/5000000000 : ℝ)*X 0 0+(1946113989/5000000000 : ℝ)*X 0 1+(4578172583/10000000000 : ℝ)*X 0 2+(2112121527/5000000000 : ℝ)*X 1 0+(1946113989/5000000000 : ℝ)*X 1 1+(4578172583/10000000000 : ℝ)*X 1 2+(2112121527/5000000000 : ℝ)*X 2 0+(1946113989/5000000000 : ℝ)*X 2 1+(4578172583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-108765273/625000000 : ℝ)*X 0 0+(5181473497/10000000000 : ℝ)*X 0 1+(5461627851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2112209027/5000000000 : ℝ)*X 0 0+(2286553633/5000000000 : ℝ)*X 0 1+(3897346603/10000000000 : ℝ)*X 0 2+(2112209027/5000000000 : ℝ)*X 1 0+(2286553633/5000000000 : ℝ)*X 1 1+(3897346603/10000000000 : ℝ)*X 1 2+(2112209027/5000000000 : ℝ)*X 2 0+(2286553633/5000000000 : ℝ)*X 2 1+(3897346603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1993611452699958120186770361/753125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (473588237/100000000000000 : ℝ)*(base19) + (424017897/100000000000000 : ℝ)*(base23) + (167013/1000000000000 : ℝ)*(lower2) + (78995873/100000000000000 : ℝ)*(upper3) + (40044173/100000000000000 : ℝ)*(upper5) + (1243582121226409/50000000000000 : ℝ)*(major0) + (1243582121226409/50000000000000 : ℝ)*(major1) + (1243582121226409/50000000000000 : ℝ)*(major2) + (1758237444112007/50000000000000 : ℝ)*(sp0) + (3516479704310941/100000000000000 : ℝ)*(sp1) + (10988999230879/312500000000 : ℝ)*(sp2) + (29156915072849/2000000000000 : ℝ)*(sp3) + (1322418791/25000000000000 : ℝ)*(sp4) + (154070419/6250000000000 : ℝ)*(sp5) + (728924109384577/50000000000000 : ℝ)*(f.failure) + (1758240088949589/50000000000000 : ℝ)*(f.sum) + (40192053744621/15062500000000000000000000000 : ℝ)*base65 + (47466374542797318213/3012500000000000000000000000000000 : ℝ)*base68 + (3845407951422318213/3012500000000000000000000000000000 : ℝ)*base70 + (27820613153684818213/3012500000000000000000000000000000 : ℝ)*base72 + (60780938245879/15062500000000000000000000000 : ℝ)*base74 + (14753445923772318213/3012500000000000000000000000000000 : ℝ)*base76 + (3846596159747318213/3012500000000000000000000000000000 : ℝ)*base78 + (6651341885152681787/3012500000000000000000000000000000 : ℝ)*base79 + (25686827262871/15062500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (32463589/5000000000000000000000 : ℝ)*base89 + (32463589/5000000000000000000000 : ℝ)*base91 + (32463589/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1596_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (517/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1596_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1596_box_0 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1461037353/10000000000 : ℝ)*x 0 + (2710851399/5000000000 : ℝ)*x 1 + (216868097/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1461037353/10000000000 : ℝ)^4703 ≤ (8553740503283/100000000000000 : ℝ)^3679 := by
    have hnat : (1461037353 : ℕ)^4703*100000000000000^3679 ≤ 8553740503283^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461037353 10000000000 8553740503283 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710851399/5000000000 : ℝ)^4703 ≤ (45723131747887/100000000000000 : ℝ)^3679 := by
    have hnat : (2710851399 : ℕ)^4703*100000000000000^3679 ≤ 45723131747887^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710851399 5000000000 45723131747887 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216868097/400000000 : ℝ)^4703 ≤ (457231277267/1000000000000 : ℝ)^3679 := by
    have hnat : (216868097 : ℕ)^4703*1000000000000^3679 ≤ 457231277267^3679*400000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216868097 400000000 457231277267 1000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1461037353/10000000000 : ℝ), (2710851399/5000000000 : ℝ), (216868097/400000000 : ℝ)] ![(8553740503283/100000000000000 : ℝ), (45723131747887/100000000000000 : ℝ), (457231277267/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1461037353/10000000000 : ℝ)|^4703 ≤ (8553740503283/100000000000000 : ℝ)^3679
        have hw : |(-1461037353/10000000000 : ℝ)|=(1461037353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710851399/5000000000 : ℝ)|^4703 ≤ (45723131747887/100000000000000 : ℝ)^3679
        have hw : |(2710851399/5000000000 : ℝ)|=(2710851399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216868097/400000000 : ℝ)|^4703 ≤ (457231277267/1000000000000 : ℝ)^3679
        have hw : |(216868097/400000000 : ℝ)|=(216868097/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_1 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164091317/312500000 : ℝ)*x 0 + (-212585871/1250000000 : ℝ)*x 1 + (2168681/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164091317/312500000 : ℝ)^4703 ≤ (21945068071307/50000000000000 : ℝ)^3679 := by
    have hnat : (164091317 : ℕ)^4703*50000000000000^3679 ≤ 21945068071307^3679*312500000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164091317 312500000 21945068071307 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212585871/1250000000 : ℝ)^4703 ≤ (5193367651889/50000000000000 : ℝ)^3679 := by
    have hnat : (212585871 : ℕ)^4703*50000000000000^3679 ≤ 5193367651889^3679*1250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212585871 1250000000 5193367651889 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168681/4000000 : ℝ)^4703 ≤ (45723128535249/100000000000000 : ℝ)^3679 := by
    have hnat : (2168681 : ℕ)^4703*100000000000000^3679 ≤ 45723128535249^3679*4000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168681 4000000 45723128535249 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164091317/312500000 : ℝ), (-212585871/1250000000 : ℝ), (2168681/4000000 : ℝ)] ![(21945068071307/50000000000000 : ℝ), (5193367651889/50000000000000 : ℝ), (45723128535249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164091317/312500000 : ℝ)|^4703 ≤ (21945068071307/50000000000000 : ℝ)^3679
        have hw : |(164091317/312500000 : ℝ)|=(164091317/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212585871/1250000000 : ℝ)|^4703 ≤ (5193367651889/50000000000000 : ℝ)^3679
        have hw : |(-212585871/1250000000 : ℝ)|=(212585871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2168681/4000000 : ℝ)|^4703 ≤ (45723128535249/100000000000000 : ℝ)^3679
        have hw : |(2168681/4000000 : ℝ)|=(2168681/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_2 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262546093/500000000 : ℝ)*x 0 + (216868103/400000000 : ℝ)*x 1 + (-850343627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262546093/500000000 : ℝ)^4703 ≤ (2194506655403/5000000000000 : ℝ)^3679 := by
    have hnat : (262546093 : ℕ)^4703*5000000000000^3679 ≤ 2194506655403^3679*500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262546093 500000000 2194506655403 5000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216868103/400000000 : ℝ)^4703 ≤ (45723129343799/100000000000000 : ℝ)^3679 := by
    have hnat : (216868103 : ℕ)^4703*100000000000000^3679 ≤ 45723129343799^3679*400000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216868103 400000000 45723129343799 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850343627/5000000000 : ℝ)^4703 ≤ (10386737536661/100000000000000 : ℝ)^3679 := by
    have hnat : (850343627 : ℕ)^4703*100000000000000^3679 ≤ 10386737536661^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850343627 5000000000 10386737536661 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262546093/500000000 : ℝ), (216868103/400000000 : ℝ), (-850343627/5000000000 : ℝ)] ![(2194506655403/5000000000000 : ℝ), (45723129343799/100000000000000 : ℝ), (10386737536661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262546093/500000000 : ℝ)|^4703 ≤ (2194506655403/5000000000000 : ℝ)^3679
        have hw : |(262546093/500000000 : ℝ)|=(262546093/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216868103/400000000 : ℝ)|^4703 ≤ (45723129343799/100000000000000 : ℝ)^3679
        have hw : |(216868103/400000000 : ℝ)|=(216868103/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-850343627/5000000000 : ℝ)|^4703 ≤ (10386737536661/100000000000000 : ℝ)^3679
        have hw : |(-850343627/5000000000 : ℝ)|=(850343627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_3 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4505380027/10000000000 : ℝ)*x 0 + (512085627/1250000000 : ℝ)*x 1 + (2048342279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4505380027/10000000000 : ℝ)^4703 ≤ (18043560918961/50000000000000 : ℝ)^3679 := by
    have hnat : (4505380027 : ℕ)^4703*50000000000000^3679 ≤ 18043560918961^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505380027 10000000000 18043560918961 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512085627/1250000000 : ℝ)^4703 ≤ (15978220677651/50000000000000 : ℝ)^3679 := by
    have hnat : (512085627 : ℕ)^4703*50000000000000^3679 ≤ 15978220677651^3679*1250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512085627 1250000000 15978220677651 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048342279/5000000000 : ℝ)^4703 ≤ (7989109197061/25000000000000 : ℝ)^3679 := by
    have hnat : (2048342279 : ℕ)^4703*25000000000000^3679 ≤ 7989109197061^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048342279 5000000000 7989109197061 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4505380027/10000000000 : ℝ), (512085627/1250000000 : ℝ), (2048342279/5000000000 : ℝ)] ![(18043560918961/50000000000000 : ℝ), (15978220677651/50000000000000 : ℝ), (7989109197061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4505380027/10000000000 : ℝ)|^4703 ≤ (18043560918961/50000000000000 : ℝ)^3679
        have hw : |(4505380027/10000000000 : ℝ)|=(4505380027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512085627/1250000000 : ℝ)|^4703 ≤ (15978220677651/50000000000000 : ℝ)^3679
        have hw : |(512085627/1250000000 : ℝ)|=(512085627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2048342279/5000000000 : ℝ)|^4703 ≤ (7989109197061/25000000000000 : ℝ)^3679
        have hw : |(2048342279/5000000000 : ℝ)|=(2048342279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_4 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2030098327/10000000000 : ℝ)*x 0 + (1303301867/2500000000 : ℝ)*x 1 + (1042641589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030098327/10000000000 : ℝ)^4703 ≤ (13024881958223/100000000000000 : ℝ)^3679 := by
    have hnat : (2030098327 : ℕ)^4703*100000000000000^3679 ≤ 13024881958223^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030098327 10000000000 13024881958223 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303301867/2500000000 : ℝ)^4703 ≤ (8697511294197/20000000000000 : ℝ)^3679 := by
    have hnat : (1303301867 : ℕ)^4703*20000000000000^3679 ≤ 8697511294197^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303301867 2500000000 8697511294197 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042641589/2000000000 : ℝ)^4703 ≤ (21743780778769/50000000000000 : ℝ)^3679 := by
    have hnat : (1042641589 : ℕ)^4703*50000000000000^3679 ≤ 21743780778769^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042641589 2000000000 21743780778769 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2030098327/10000000000 : ℝ), (1303301867/2500000000 : ℝ), (1042641589/2000000000 : ℝ)] ![(13024881958223/100000000000000 : ℝ), (8697511294197/20000000000000 : ℝ), (21743780778769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2030098327/10000000000 : ℝ)|^4703 ≤ (13024881958223/100000000000000 : ℝ)^3679
        have hw : |(-2030098327/10000000000 : ℝ)|=(2030098327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303301867/2500000000 : ℝ)|^4703 ≤ (8697511294197/20000000000000 : ℝ)^3679
        have hw : |(1303301867/2500000000 : ℝ)|=(1303301867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042641589/2000000000 : ℝ)|^4703 ≤ (21743780778769/50000000000000 : ℝ)^3679
        have hw : |(1042641589/2000000000 : ℝ)|=(1042641589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_5 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395107837/10000000000 : ℝ)*x 0 + (-1788327783/10000000000 : ℝ)*x 1 + (2606604091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395107837/10000000000 : ℝ)^4703 ≤ (22718308202407/50000000000000 : ℝ)^3679 := by
    have hnat : (5395107837 : ℕ)^4703*50000000000000^3679 ≤ 22718308202407^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395107837 10000000000 22718308202407 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1788327783/10000000000 : ℝ)^4703 ≤ (5537909745429/50000000000000 : ℝ)^3679 := by
    have hnat : (1788327783 : ℕ)^4703*50000000000000^3679 ≤ 5537909745429^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788327783 10000000000 5537909745429 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606604091/5000000000 : ℝ)^4703 ≤ (43487564084819/100000000000000 : ℝ)^3679 := by
    have hnat : (2606604091 : ℕ)^4703*100000000000000^3679 ≤ 43487564084819^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606604091 5000000000 43487564084819 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395107837/10000000000 : ℝ), (-1788327783/10000000000 : ℝ), (2606604091/5000000000 : ℝ)] ![(22718308202407/50000000000000 : ℝ), (5537909745429/50000000000000 : ℝ), (43487564084819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395107837/10000000000 : ℝ)|^4703 ≤ (22718308202407/50000000000000 : ℝ)^3679
        have hw : |(5395107837/10000000000 : ℝ)|=(5395107837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1788327783/10000000000 : ℝ)|^4703 ≤ (5537909745429/50000000000000 : ℝ)^3679
        have hw : |(-1788327783/10000000000 : ℝ)|=(1788327783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606604091/5000000000 : ℝ)|^4703 ≤ (43487564084819/100000000000000 : ℝ)^3679
        have hw : |(2606604091/5000000000 : ℝ)|=(2606604091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_6 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079021823/2000000000 : ℝ)*x 0 + (5213206727/10000000000 : ℝ)*x 1 + (-894164003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079021823/2000000000 : ℝ)^4703 ≤ (45436630163657/100000000000000 : ℝ)^3679 := by
    have hnat : (1079021823 : ℕ)^4703*100000000000000^3679 ≤ 45436630163657^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079021823 2000000000 45436630163657 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213206727/10000000000 : ℝ)^4703 ≤ (43487548569233/100000000000000 : ℝ)^3679 := by
    have hnat : (5213206727 : ℕ)^4703*100000000000000^3679 ≤ 43487548569233^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213206727 10000000000 43487548569233 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894164003/5000000000 : ℝ)^4703 ≤ (11075821256403/100000000000000 : ℝ)^3679 := by
    have hnat : (894164003 : ℕ)^4703*100000000000000^3679 ≤ 11075821256403^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894164003 5000000000 11075821256403 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079021823/2000000000 : ℝ), (5213206727/10000000000 : ℝ), (-894164003/5000000000 : ℝ)] ![(45436630163657/100000000000000 : ℝ), (43487548569233/100000000000000 : ℝ), (11075821256403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079021823/2000000000 : ℝ)|^4703 ≤ (45436630163657/100000000000000 : ℝ)^3679
        have hw : |(1079021823/2000000000 : ℝ)|=(1079021823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213206727/10000000000 : ℝ)|^4703 ≤ (43487548569233/100000000000000 : ℝ)^3679
        have hw : |(5213206727/10000000000 : ℝ)|=(5213206727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-894164003/5000000000 : ℝ)|^4703 ≤ (11075821256403/100000000000000 : ℝ)^3679
        have hw : |(-894164003/5000000000 : ℝ)|=(894164003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_7 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (787493727/2000000000 : ℝ)*x 0 + (4380289037/10000000000 : ℝ)*x 1 + (4380289903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787493727/2000000000 : ℝ)^4703 ≤ (30377445606389/100000000000000 : ℝ)^3679 := by
    have hnat : (787493727 : ℕ)^4703*100000000000000^3679 ≤ 30377445606389^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787493727 2000000000 30377445606389 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4380289037/10000000000 : ℝ)^4703 ≤ (34811272790779/100000000000000 : ℝ)^3679 := by
    have hnat : (4380289037 : ℕ)^4703*100000000000000^3679 ≤ 34811272790779^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380289037 10000000000 34811272790779 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4380289903/10000000000 : ℝ)^4703 ≤ (34811281588703/100000000000000 : ℝ)^3679 := by
    have hnat : (4380289903 : ℕ)^4703*100000000000000^3679 ≤ 34811281588703^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380289903 10000000000 34811281588703 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(787493727/2000000000 : ℝ), (4380289037/10000000000 : ℝ), (4380289903/10000000000 : ℝ)] ![(30377445606389/100000000000000 : ℝ), (34811272790779/100000000000000 : ℝ), (34811281588703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(787493727/2000000000 : ℝ)|^4703 ≤ (30377445606389/100000000000000 : ℝ)^3679
        have hw : |(787493727/2000000000 : ℝ)|=(787493727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4380289037/10000000000 : ℝ)|^4703 ≤ (34811272790779/100000000000000 : ℝ)^3679
        have hw : |(4380289037/10000000000 : ℝ)|=(4380289037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4380289903/10000000000 : ℝ)|^4703 ≤ (34811281588703/100000000000000 : ℝ)^3679
        have hw : |(4380289903/10000000000 : ℝ)|=(4380289903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_8 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1909278521/10000000000 : ℝ)*x 0 + (5064648003/10000000000 : ℝ)*x 1 + (5451815231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1909278521/10000000000 : ℝ)^4703 ≤ (6021143285087/50000000000000 : ℝ)^3679 := by
    have hnat : (1909278521 : ℕ)^4703*50000000000000^3679 ≤ 6021143285087^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909278521 10000000000 6021143285087 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5064648003/10000000000 : ℝ)^4703 ≤ (41909699092253/100000000000000 : ℝ)^3679 := by
    have hnat : (5064648003 : ℕ)^4703*100000000000000^3679 ≤ 41909699092253^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5064648003 10000000000 41909699092253 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451815231/10000000000 : ℝ)^4703 ≤ (5756001789549/12500000000000 : ℝ)^3679 := by
    have hnat : (5451815231 : ℕ)^4703*12500000000000^3679 ≤ 5756001789549^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451815231 10000000000 5756001789549 12500000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1909278521/10000000000 : ℝ), (5064648003/10000000000 : ℝ), (5451815231/10000000000 : ℝ)] ![(6021143285087/50000000000000 : ℝ), (41909699092253/100000000000000 : ℝ), (5756001789549/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1909278521/10000000000 : ℝ)|^4703 ≤ (6021143285087/50000000000000 : ℝ)^3679
        have hw : |(-1909278521/10000000000 : ℝ)|=(1909278521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5064648003/10000000000 : ℝ)|^4703 ≤ (41909699092253/100000000000000 : ℝ)^3679
        have hw : |(5064648003/10000000000 : ℝ)|=(5064648003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451815231/10000000000 : ℝ)|^4703 ≤ (5756001789549/12500000000000 : ℝ)^3679
        have hw : |(5451815231/10000000000 : ℝ)|=(5451815231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_9 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230090313/10000000000 : ℝ)*x 0 + (-52736071/312500000 : ℝ)*x 1 + (545181529/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230090313/10000000000 : ℝ)^4703 ≤ (10916917502363/25000000000000 : ℝ)^3679 := by
    have hnat : (5230090313 : ℕ)^4703*25000000000000^3679 ≤ 10916917502363^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230090313 10000000000 10916917502363 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52736071/312500000 : ℝ)^4703 ≤ (2056863006429/20000000000000 : ℝ)^3679 := by
    have hnat : (52736071 : ℕ)^4703*20000000000000^3679 ≤ 2056863006429^3679*312500000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52736071 312500000 2056863006429 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545181529/1000000000 : ℝ)^4703 ≤ (5756001869179/12500000000000 : ℝ)^3679 := by
    have hnat : (545181529 : ℕ)^4703*12500000000000^3679 ≤ 5756001869179^3679*1000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545181529 1000000000 5756001869179 12500000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230090313/10000000000 : ℝ), (-52736071/312500000 : ℝ), (545181529/1000000000 : ℝ)] ![(10916917502363/25000000000000 : ℝ), (2056863006429/20000000000000 : ℝ), (5756001869179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230090313/10000000000 : ℝ)|^4703 ≤ (10916917502363/25000000000000 : ℝ)^3679
        have hw : |(5230090313/10000000000 : ℝ)|=(5230090313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52736071/312500000 : ℝ)|^4703 ≤ (2056863006429/20000000000000 : ℝ)^3679
        have hw : |(-52736071/312500000 : ℝ)|=(52736071/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545181529/1000000000 : ℝ)|^4703 ≤ (5756001869179/12500000000000 : ℝ)^3679
        have hw : |(545181529/1000000000 : ℝ)|=(545181529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_10 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615045541/5000000000 : ℝ)*x 0 + (1090363089/2000000000 : ℝ)*x 1 + (-1687553003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615045541/5000000000 : ℝ)^4703 ≤ (43667678217169/100000000000000 : ℝ)^3679 := by
    have hnat : (2615045541 : ℕ)^4703*100000000000000^3679 ≤ 43667678217169^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615045541 5000000000 43667678217169 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090363089/2000000000 : ℝ)^4703 ≤ (46048016627013/100000000000000 : ℝ)^3679 := by
    have hnat : (1090363089 : ℕ)^4703*100000000000000^3679 ≤ 46048016627013^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090363089 2000000000 46048016627013 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1687553003/10000000000 : ℝ)^4703 ≤ (10284305146059/100000000000000 : ℝ)^3679 := by
    have hnat : (1687553003 : ℕ)^4703*100000000000000^3679 ≤ 10284305146059^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687553003 10000000000 10284305146059 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615045541/5000000000 : ℝ), (1090363089/2000000000 : ℝ), (-1687553003/10000000000 : ℝ)] ![(43667678217169/100000000000000 : ℝ), (46048016627013/100000000000000 : ℝ), (10284305146059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615045541/5000000000 : ℝ)|^4703 ≤ (43667678217169/100000000000000 : ℝ)^3679
        have hw : |(2615045541/5000000000 : ℝ)|=(2615045541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090363089/2000000000 : ℝ)|^4703 ≤ (46048016627013/100000000000000 : ℝ)^3679
        have hw : |(1090363089/2000000000 : ℝ)|=(1090363089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1687553003/10000000000 : ℝ)|^4703 ≤ (10284305146059/100000000000000 : ℝ)^3679
        have hw : |(-1687553003/10000000000 : ℝ)|=(1687553003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_11 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4584998179/10000000000 : ℝ)*x 0 + (4055651221/10000000000 : ℝ)*x 1 + (4055649827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4584998179/10000000000 : ℝ)^4703 ≤ (36904344454717/100000000000000 : ℝ)^3679 := by
    have hnat : (4584998179 : ℕ)^4703*100000000000000^3679 ≤ 36904344454717^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584998179 10000000000 36904344454717 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4055651221/10000000000 : ℝ)^4703 ≤ (6309566940103/20000000000000 : ℝ)^3679 := by
    have hnat : (4055651221 : ℕ)^4703*20000000000000^3679 ≤ 6309566940103^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4055651221 10000000000 6309566940103 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4055649827/10000000000 : ℝ)^4703 ≤ (15773910419401/50000000000000 : ℝ)^3679 := by
    have hnat : (4055649827 : ℕ)^4703*50000000000000^3679 ≤ 15773910419401^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4055649827 10000000000 15773910419401 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4584998179/10000000000 : ℝ), (4055651221/10000000000 : ℝ), (4055649827/10000000000 : ℝ)] ![(36904344454717/100000000000000 : ℝ), (6309566940103/20000000000000 : ℝ), (15773910419401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4584998179/10000000000 : ℝ)|^4703 ≤ (36904344454717/100000000000000 : ℝ)^3679
        have hw : |(4584998179/10000000000 : ℝ)|=(4584998179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4055651221/10000000000 : ℝ)|^4703 ≤ (6309566940103/20000000000000 : ℝ)^3679
        have hw : |(4055651221/10000000000 : ℝ)|=(4055651221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4055649827/10000000000 : ℝ)|^4703 ≤ (15773910419401/50000000000000 : ℝ)^3679
        have hw : |(4055649827/10000000000 : ℝ)|=(4055649827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_12 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-316171283/2000000000 : ℝ)*x 0 + (5564084537/10000000000 : ℝ)*x 1 + (1298334899/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (316171283/2000000000 : ℝ)^4703 ≤ (9460518602513/100000000000000 : ℝ)^3679 := by
    have hnat : (316171283 : ℕ)^4703*100000000000000^3679 ≤ 9460518602513^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316171283 2000000000 9460518602513 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5564084537/10000000000 : ℝ)^4703 ≤ (23631838065459/50000000000000 : ℝ)^3679 := by
    have hnat : (5564084537 : ℕ)^4703*50000000000000^3679 ≤ 23631838065459^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5564084537 10000000000 23631838065459 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298334899/2500000000 : ℝ)^4703 ≤ (21637902623891/50000000000000 : ℝ)^3679 := by
    have hnat : (1298334899 : ℕ)^4703*50000000000000^3679 ≤ 21637902623891^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298334899 2500000000 21637902623891 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-316171283/2000000000 : ℝ), (5564084537/10000000000 : ℝ), (1298334899/2500000000 : ℝ)] ![(9460518602513/100000000000000 : ℝ), (23631838065459/50000000000000 : ℝ), (21637902623891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-316171283/2000000000 : ℝ)|^4703 ≤ (9460518602513/100000000000000 : ℝ)^3679
        have hw : |(-316171283/2000000000 : ℝ)|=(316171283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5564084537/10000000000 : ℝ)|^4703 ≤ (23631838065459/50000000000000 : ℝ)^3679
        have hw : |(5564084537/10000000000 : ℝ)|=(5564084537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298334899/2500000000 : ℝ)|^4703 ≤ (21637902623891/50000000000000 : ℝ)^3679
        have hw : |(1298334899/2500000000 : ℝ)|=(1298334899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_13 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5408853931/10000000000 : ℝ)*x 0 + (-1796370883/10000000000 : ℝ)*x 1 + (5193339417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5408853931/10000000000 : ℝ)^4703 ≤ (45584658160069/100000000000000 : ℝ)^3679 := by
    have hnat : (5408853931 : ℕ)^4703*100000000000000^3679 ≤ 45584658160069^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408853931 10000000000 45584658160069 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1796370883/10000000000 : ℝ)^4703 ≤ (2784884619307/25000000000000 : ℝ)^3679 := by
    have hnat : (1796370883 : ℕ)^4703*25000000000000^3679 ≤ 2784884619307^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796370883 10000000000 2784884619307 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193339417/10000000000 : ℝ)^4703 ≤ (2163790167051/5000000000000 : ℝ)^3679 := by
    have hnat : (5193339417 : ℕ)^4703*5000000000000^3679 ≤ 2163790167051^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193339417 10000000000 2163790167051 5000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5408853931/10000000000 : ℝ), (-1796370883/10000000000 : ℝ), (5193339417/10000000000 : ℝ)] ![(45584658160069/100000000000000 : ℝ), (2784884619307/25000000000000 : ℝ), (2163790167051/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5408853931/10000000000 : ℝ)|^4703 ≤ (45584658160069/100000000000000 : ℝ)^3679
        have hw : |(5408853931/10000000000 : ℝ)|=(5408853931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1796370883/10000000000 : ℝ)|^4703 ≤ (2784884619307/25000000000000 : ℝ)^3679
        have hw : |(-1796370883/10000000000 : ℝ)|=(1796370883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193339417/10000000000 : ℝ)|^4703 ≤ (2163790167051/5000000000000 : ℝ)^3679
        have hw : |(5193339417/10000000000 : ℝ)|=(5193339417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_14 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2704426961/5000000000 : ℝ)*x 0 + (2596669697/5000000000 : ℝ)*x 1 + (-898185463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704426961/5000000000 : ℝ)^4703 ≤ (45584658063107/100000000000000 : ℝ)^3679 := by
    have hnat : (2704426961 : ℕ)^4703*100000000000000^3679 ≤ 45584658063107^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704426961 5000000000 45584658063107 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596669697/5000000000 : ℝ)^4703 ≤ (43275803096017/100000000000000 : ℝ)^3679 := by
    have hnat : (2596669697 : ℕ)^4703*100000000000000^3679 ≤ 43275803096017^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596669697 5000000000 43275803096017 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898185463/5000000000 : ℝ)^4703 ≤ (2227907763619/20000000000000 : ℝ)^3679 := by
    have hnat : (898185463 : ℕ)^4703*20000000000000^3679 ≤ 2227907763619^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898185463 5000000000 2227907763619 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704426961/5000000000 : ℝ), (2596669697/5000000000 : ℝ), (-898185463/5000000000 : ℝ)] ![(45584658063107/100000000000000 : ℝ), (43275803096017/100000000000000 : ℝ), (2227907763619/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704426961/5000000000 : ℝ)|^4703 ≤ (45584658063107/100000000000000 : ℝ)^3679
        have hw : |(2704426961/5000000000 : ℝ)|=(2704426961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596669697/5000000000 : ℝ)|^4703 ≤ (43275803096017/100000000000000 : ℝ)^3679
        have hw : |(2596669697/5000000000 : ℝ)|=(2596669697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-898185463/5000000000 : ℝ)|^4703 ≤ (2227907763619/20000000000000 : ℝ)^3679
        have hw : |(-898185463/5000000000 : ℝ)|=(898185463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_box_15 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1940864961/5000000000 : ℝ)*x 0 + (4407267633/10000000000 : ℝ)*x 1 + (2203633857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1940864961/5000000000 : ℝ)^4703 ≤ (1864301184473/6250000000000 : ℝ)^3679 := by
    have hnat : (1940864961 : ℕ)^4703*6250000000000^3679 ≤ 1864301184473^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940864961 5000000000 1864301184473 6250000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4407267633/10000000000 : ℝ)^4703 ≤ (17542795051153/50000000000000 : ℝ)^3679 := by
    have hnat : (4407267633 : ℕ)^4703*50000000000000^3679 ≤ 17542795051153^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407267633 10000000000 17542795051153 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203633857/5000000000 : ℝ)^4703 ≤ (17542795463307/50000000000000 : ℝ)^3679 := by
    have hnat : (2203633857 : ℕ)^4703*50000000000000^3679 ≤ 17542795463307^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203633857 5000000000 17542795463307 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1940864961/5000000000 : ℝ), (4407267633/10000000000 : ℝ), (2203633857/5000000000 : ℝ)] ![(1864301184473/6250000000000 : ℝ), (17542795051153/50000000000000 : ℝ), (17542795463307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1940864961/5000000000 : ℝ)|^4703 ≤ (1864301184473/6250000000000 : ℝ)^3679
        have hw : |(1940864961/5000000000 : ℝ)|=(1940864961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4407267633/10000000000 : ℝ)|^4703 ≤ (17542795051153/50000000000000 : ℝ)^3679
        have hw : |(4407267633/10000000000 : ℝ)|=(4407267633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2203633857/5000000000 : ℝ)|^4703 ≤ (17542795463307/50000000000000 : ℝ)^3679
        have hw : |(2203633857/5000000000 : ℝ)|=(2203633857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1596_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (517/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(64877/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58043/100000 : ℝ) ∧ (80149/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (87679/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (517/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (517/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (517/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (517/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (517/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (517/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (517/5000 : ℝ) ^ (4699/1024 : ℝ) ≤ (1502227267246059/50000000000000000000 : ℝ) := by
    have hpowers : (517/5000 : ℝ)^4699 ≤ (1502227267246059/50000000000000000000 : ℝ)^1024 := by
      have hnat : (517 : ℕ)^4699*50000000000000000000^1024 ≤ 1502227267246059^1024*5000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        517 5000 1502227267246059 50000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (517/5000 : ℝ)) (X := (1502227267246059/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4091/25000 : ℝ) ^ (4699/1024 : ℝ) ≤ (4939388458165287/20000000000000000000 : ℝ) := by
    have hpowers : (4091/25000 : ℝ)^4699 ≤ (4939388458165287/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4091 : ℕ)^4699*20000000000000000000^1024 ≤ 4939388458165287^1024*25000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4091 25000 4939388458165287 20000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4091/25000 : ℝ)) (X := (4939388458165287/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001502227267246059/25000000000000000000 : ℝ) ≤ (5000065471146097/5000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (25001502227267246059/25000000000000000000 : ℝ)^1024 ≤ (5000065471146097/5000000000000000 : ℝ)^4699 := by
      have hnat : (25001502227267246059 : ℕ)^1024*5000000000000000^4699 ≤ 5000065471146097^4699*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001502227267246059 25000000000000000000 5000065471146097 5000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000065471146097/5000000000000000 : ℝ)) (X := (25001502227267246059/25000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027701396825318553/100000000000000000000 : ℝ) ≤ (10000603599874847/10000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (100027701396825318553/100000000000000000000 : ℝ)^1024 ≤ (10000603599874847/10000000000000000 : ℝ)^4699 := by
      have hnat : (100027701396825318553 : ℕ)^1024*10000000000000000^4699 ≤ 10000603599874847^4699*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027701396825318553 100000000000000000000 10000603599874847 10000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000603599874847/10000000000000000 : ℝ)) (X := (100027701396825318553/100000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004939388458165287/10000000000000000000 : ℝ) ≤ (4000430502983/4000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (10004939388458165287/10000000000000000000 : ℝ)^1024 ≤ (4000430502983/4000000000000 : ℝ)^4699 := by
      have hnat : (10004939388458165287 : ℕ)^1024*4000000000000^4699 ≤ 4000430502983^4699*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004939388458165287 10000000000000000000 4000430502983 4000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (4000430502983/4000000000000 : ℝ)) (X := (10004939388458165287/10000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1502227267246059/50000000000000000000 : ℝ) ≤ ((2509625593231621359/2510000000000000000 : ℝ)+2*(157552527551/200800000000000 : ℝ)*(517/5000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (2509625593231621359/2510000000000000000 : ℝ)+2*(157552527551/200800000000000 : ℝ)*(517/5000 : ℝ)=(5000065471146097/5000000000000000 : ℝ) by norm_num, show 1+2*(1502227267246059/50000000000000000000 : ℝ)=(25001502227267246059/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4939388458165287/20000000000000000000 : ℝ)+(1502227267246059/50000000000000000000 : ℝ) ≤ ((2509625593231621359/2510000000000000000 : ℝ)+(157552527551/200800000000000 : ℝ)*((4091/25000 : ℝ)+(517/5000 : ℝ)))^(4699/1024 : ℝ) := by
    rw [show (2509625593231621359/2510000000000000000 : ℝ)+(157552527551/200800000000000 : ℝ)*((4091/25000 : ℝ)+(517/5000 : ℝ))=(10000603599874847/10000000000000000 : ℝ) by norm_num, show 1+(4939388458165287/20000000000000000000 : ℝ)+(1502227267246059/50000000000000000000 : ℝ)=(100027701396825318553/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4939388458165287/20000000000000000000 : ℝ) ≤ ((2509625593231621359/2510000000000000000 : ℝ)+2*(157552527551/200800000000000 : ℝ)*(4091/25000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (2509625593231621359/2510000000000000000 : ℝ)+2*(157552527551/200800000000000 : ℝ)*(4091/25000 : ℝ)=(4000430502983/4000000000000 : ℝ) by norm_num, show 1+2*(4939388458165287/20000000000000000000 : ℝ)=(10004939388458165287/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2509625593231621359/2510000000000000000 : ℝ)*(X 1 0+X 2 0)+(157552527551/200800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (517/5000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (2509625593231621359/2510000000000000000 : ℝ)) (alpha := (157552527551/200800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2509625593231621359/2510000000000000000 : ℝ)*(X 0 1+X 2 1)+(157552527551/200800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (517/5000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (2509625593231621359/2510000000000000000 : ℝ)) (alpha := (157552527551/200800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2509625593231621359/2510000000000000000 : ℝ)*(X 0 2+X 1 2)+(157552527551/200800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (517/5000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (2509625593231621359/2510000000000000000 : ℝ)) (alpha := (157552527551/200800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1461037353/10000000000 : ℝ)*X 0 0+(2710851399/5000000000 : ℝ)*X 0 1+(216868097/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((164091317/312500000 : ℝ)*X 1 0+(-212585871/1250000000 : ℝ)*X 1 1+(2168681/4000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((262546093/500000000 : ℝ)*X 2 0+(216868103/400000000 : ℝ)*X 2 1+(-850343627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4505380027/10000000000 : ℝ)*X 0 0+(512085627/1250000000 : ℝ)*X 0 1+(2048342279/5000000000 : ℝ)*X 0 2+(4505380027/10000000000 : ℝ)*X 1 0+(512085627/1250000000 : ℝ)*X 1 1+(2048342279/5000000000 : ℝ)*X 1 2+(4505380027/10000000000 : ℝ)*X 2 0+(512085627/1250000000 : ℝ)*X 2 1+(2048342279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2030098327/10000000000 : ℝ)*X 0 0+(1303301867/2500000000 : ℝ)*X 0 1+(1042641589/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5395107837/10000000000 : ℝ)*X 1 0+(-1788327783/10000000000 : ℝ)*X 1 1+(2606604091/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1079021823/2000000000 : ℝ)*X 2 0+(5213206727/10000000000 : ℝ)*X 2 1+(-894164003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((787493727/2000000000 : ℝ)*X 0 0+(4380289037/10000000000 : ℝ)*X 0 1+(4380289903/10000000000 : ℝ)*X 0 2+(787493727/2000000000 : ℝ)*X 1 0+(4380289037/10000000000 : ℝ)*X 1 1+(4380289903/10000000000 : ℝ)*X 1 2+(787493727/2000000000 : ℝ)*X 2 0+(4380289037/10000000000 : ℝ)*X 2 1+(4380289903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1909278521/10000000000 : ℝ)*X 0 0+(5064648003/10000000000 : ℝ)*X 0 1+(5451815231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230090313/10000000000 : ℝ)*X 1 0+(-52736071/312500000 : ℝ)*X 1 1+(545181529/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2615045541/5000000000 : ℝ)*X 2 0+(1090363089/2000000000 : ℝ)*X 2 1+(-1687553003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4584998179/10000000000 : ℝ)*X 0 0+(4055651221/10000000000 : ℝ)*X 0 1+(4055649827/10000000000 : ℝ)*X 0 2+(4584998179/10000000000 : ℝ)*X 1 0+(4055651221/10000000000 : ℝ)*X 1 1+(4055649827/10000000000 : ℝ)*X 1 2+(4584998179/10000000000 : ℝ)*X 2 0+(4055651221/10000000000 : ℝ)*X 2 1+(4055649827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-316171283/2000000000 : ℝ)*X 0 0+(5564084537/10000000000 : ℝ)*X 0 1+(1298334899/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5408853931/10000000000 : ℝ)*X 1 0+(-1796370883/10000000000 : ℝ)*X 1 1+(5193339417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2704426961/5000000000 : ℝ)*X 2 0+(2596669697/5000000000 : ℝ)*X 2 1+(-898185463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1940864961/5000000000 : ℝ)*X 0 0+(4407267633/10000000000 : ℝ)*X 0 1+(2203633857/5000000000 : ℝ)*X 0 2+(1940864961/5000000000 : ℝ)*X 1 0+(4407267633/10000000000 : ℝ)*X 1 1+(2203633857/5000000000 : ℝ)*X 1 2+(1940864961/5000000000 : ℝ)*X 2 0+(4407267633/10000000000 : ℝ)*X 2 1+(2203633857/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-64877/100000 : ℝ) ≤ (-2544292335368151174608306626521/3921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19905481/100000000000000 : ℝ)*(upper0) + (38708333/100000000000000 : ℝ)*(lower2) + (36275437/50000000000000 : ℝ)*(lower3) + (96676423/100000000000000 : ℝ)*(upper5) + (25845804043983/1562500000000 : ℝ)*(major0) + (25845804043983/1562500000000 : ℝ)*(major1) + (25845804043983/1562500000000 : ℝ)*(major2) + (6035388743/50000000000000 : ℝ)*(sp2) + (1318454143/100000000000000 : ℝ)*(sp3) + (1180160310730329/50000000000000 : ℝ)*(sp4) + (590063987969679/25000000000000 : ℝ)*(sp5) + (590077137670793/25000000000000 : ℝ)*(sp6) + (484782886564253/50000000000000 : ℝ)*(sp7) + (32334790971/50000000000000 : ℝ)*(sp13) + (969567091582649/100000000000000 : ℝ)*(f.failure) + (1180160310730329/50000000000000 : ℝ)*(f.sum) + (417953261211/1255000000000000000000000000 : ℝ)*base66 + (22557481351551647/3921875000000000000000000000000 : ℝ)*base67 + (8913974092676647/3921875000000000000000000000000 : ℝ)*base69 + (9651126251861761/1960937500000000000000000000000 : ℝ)*base71 + (2345975554271/313750000000000000000000000 : ℝ)*base73 + (4865287947114147/3921875000000000000000000000000 : ℝ)*base75 + (1086492825480767/245117187500000000000000000000 : ℝ)*base77 + (71735713100770397/3921875000000000000000000000000 : ℝ)*base79 + (72086797779/313750000000000000000000000 : ℝ)*base82 + (11120893/10000000000000000000000 : ℝ)*base89 + (11120893/10000000000000000000000 : ℝ)*base91 + (11120893/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58043/100000 : ℝ) ≤ (36423276431741245025731177249533/62750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2897381/20000000000000 : ℝ)*(lower0) + (25561023/50000000000000 : ℝ)*(upper2) + (35025239/50000000000000 : ℝ)*(upper3) + (43167451/100000000000000 : ℝ)*(lower5) + (868484018238071/50000000000000 : ℝ)*(major0) + (868484018238071/50000000000000 : ℝ)*(major1) + (868484018238071/50000000000000 : ℝ)*(major2) + (609116517667879/25000000000000 : ℝ)*(sp0) + (2436448876322081/100000000000000 : ℝ)*(sp1) + (2436457551840701/100000000000000 : ℝ)*(sp2) + (1018121347637287/100000000000000 : ℝ)*(sp3) + (300629267/100000000000000 : ℝ)*(sp7) + (3438869887/20000000000000 : ℝ)*(sp9) + (266213463/3125000000000 : ℝ)*(sp10) + (509060824133277/50000000000000 : ℝ)*(f.failure) + (609116517667879/25000000000000 : ℝ)*(f.sum) + (18183579538799/5020000000000000000000000000 : ℝ)*base66 + (11074218722570989/125500000000000000000000000000000 : ℝ)*base67 + (1093613084068570989/125500000000000000000000000000000 : ℝ)*base69 + (299014783035570989/125500000000000000000000000000000 : ℝ)*base71 + (135035903664261/5020000000000000000000000000 : ℝ)*base73 + (38790653356429011/125500000000000000000000000000000 : ℝ)*base76 + (857771672065929011/125500000000000000000000000000000 : ℝ)*base78 + (2950766587134070989/125500000000000000000000000000000 : ℝ)*base79 + (17916397074221/5020000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (11509489/5000000000000000000000 : ℝ)*base89 + (11509489/5000000000000000000000 : ℝ)*base91 + (11509489/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80149/100000 : ℝ) ≤ (100590174250149974786900419918419/125500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26301941/25000000000000 : ℝ)*(lower3) + (94497533/25000000000000 : ℝ)*(upper4) + (41353257/100000000000000 : ℝ)*(lower5) + (1845732290746149/100000000000000 : ℝ)*(major0) + (1845732290746149/100000000000000 : ℝ)*(major1) + (1845732290746149/100000000000000 : ℝ)*(major2) + (793326841/25000000000000 : ℝ)*(sp0) + (2158591717/5000000000000 : ℝ)*(sp1) + (25856161317/20000000000000 : ℝ)*(sp2) + (28958456487/50000000000000 : ℝ)*(sp3) + (322858818771383/12500000000000 : ℝ)*(sp8) + (322853818955511/12500000000000 : ℝ)*(sp9) + (2582744442671843/100000000000000 : ℝ)*(sp10) + (135226970418151/12500000000000 : ℝ)*(sp11) + (540936840129091/50000000000000 : ℝ)*(f.failure) + (645718430869607/25000000000000 : ℝ)*(f.sum) + (3361632203339/10040000000000000000000000000 : ℝ)*base65 + (1704980306421866009/251000000000000000000000000000000 : ℝ)*base68 + (1664539632197866009/251000000000000000000000000000000 : ℝ)*base70 + (1641478515739866009/251000000000000000000000000000000 : ℝ)*base72 + (36300472168741/10040000000000000000000000000 : ℝ)*base74 + (991990663233866009/251000000000000000000000000000000 : ℝ)*base76 + (1153812553961866009/251000000000000000000000000000000 : ℝ)*base78 + (649947449767866009/251000000000000000000000000000000 : ℝ)*base80 + (16466461134461/10040000000000000000000000000 : ℝ)*base82 + (20322287/5000000000000000000000 : ℝ)*base89 + (20322287/5000000000000000000000 : ℝ)*base91 + (20322287/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-87679/100000 : ℝ) ≤ (-55017303453162840843153767021031/62750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42851697/100000000000000 : ℝ)*(upper3) + (13447917/100000000000000 : ℝ)*(lower4) + (46666107/100000000000000 : ℝ)*(upper5) + (1887078349105653/100000000000000 : ℝ)*(major0) + (1887078349105653/100000000000000 : ℝ)*(major1) + (1887078349105653/100000000000000 : ℝ)*(major2) + (179776579/12500000000000 : ℝ)*(sp4) + (47305601161/100000000000000 : ℝ)*(sp5) + (11065574799/20000000000000 : ℝ)*(sp6) + (23042630551/100000000000000 : ℝ)*(sp7) + (67431807460099/2500000000000 : ℝ)*(sp12) + (2697226431015431/100000000000000 : ℝ)*(sp13) + (2697218408742597/100000000000000 : ℝ)*(sp14) + (553042789084513/50000000000000 : ℝ)*(sp15) + (1106108620799577/100000000000000 : ℝ)*(f.failure) + (168579608538537/6250000000000 : ℝ)*(f.sum) + (38056733335917/10040000000000000000000000000 : ℝ)*base66 + (1835527318713979927/251000000000000000000000000000000 : ℝ)*base67 + (144061332662020073/251000000000000000000000000000000 : ℝ)*base70 + (227153270479979927/251000000000000000000000000000000 : ℝ)*base71 + (54541001872557/10040000000000000000000000000 : ℝ)*base74 + (1540529778458979927/251000000000000000000000000000000 : ℝ)*base75 + (1011660838388979927/251000000000000000000000000000000 : ℝ)*base77 + (2583901818676979927/251000000000000000000000000000000 : ℝ)*base79 + (51419175477197/10040000000000000000000000000 : ℝ)*base82 + (381411/10000000000000000000000 : ℝ)*base90 + (381411/10000000000000000000000 : ℝ)*base92 + (381411/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1596_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (517/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64877/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58043/100000 : ℝ) else (80149/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87679/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1596_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1596_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64877/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58043/100000 : ℝ) else (80149/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87679/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1596_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1596_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64877/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58043/100000 : ℝ) else (80149/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87679/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1596_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
