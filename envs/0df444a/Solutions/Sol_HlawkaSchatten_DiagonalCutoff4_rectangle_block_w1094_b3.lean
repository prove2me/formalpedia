-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1094_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:36.735847+00:00
-- url     : https://prove2.me/submissions/b51f9f3c-ec61-425d-a5f7-cf6ec5713776

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
theorem support_rectangle_w1094_box_0 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2061551277/10000000000 : ℝ)*x 0 + (5376985503/10000000000 : ℝ)*x 1 + (2688492763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061551277/10000000000 : ℝ)^8287 ≤ (3069114374981/25000000000000 : ℝ)^6239 := by
    have hnat : (2061551277 : ℕ)^8287*25000000000000^6239 ≤ 3069114374981^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061551277 10000000000 3069114374981 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376985503/10000000000 : ℝ)^8287 ≤ (8772354223159/20000000000000 : ℝ)^6239 := by
    have hnat : (5376985503 : ℕ)^8287*20000000000000^6239 ≤ 8772354223159^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376985503 10000000000 8772354223159 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688492763/5000000000 : ℝ)^8287 ≤ (8772354273/20000000000 : ℝ)^6239 := by
    have hnat : (2688492763 : ℕ)^8287*20000000000^6239 ≤ 8772354273^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688492763 5000000000 8772354273 20000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2061551277/10000000000 : ℝ), (5376985503/10000000000 : ℝ), (2688492763/5000000000 : ℝ)] ![(3069114374981/25000000000000 : ℝ), (8772354223159/20000000000000 : ℝ), (8772354273/20000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2061551277/10000000000 : ℝ)|^8287 ≤ (3069114374981/25000000000000 : ℝ)^6239
        have hw : |(-2061551277/10000000000 : ℝ)|=(2061551277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376985503/10000000000 : ℝ)|^8287 ≤ (8772354223159/20000000000000 : ℝ)^6239
        have hw : |(5376985503/10000000000 : ℝ)|=(5376985503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688492763/5000000000 : ℝ)|^8287 ≤ (8772354273/20000000000 : ℝ)^6239
        have hw : |(2688492763/5000000000 : ℝ)|=(2688492763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_1 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295507779/10000000000 : ℝ)*x 0 + (-542981351/2500000000 : ℝ)*x 1 + (2688492723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295507779/10000000000 : ℝ)^8287 ≤ (21490580789189/50000000000000 : ℝ)^6239 := by
    have hnat : (5295507779 : ℕ)^8287*50000000000000^6239 ≤ 21490580789189^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295507779 10000000000 21490580789189 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542981351/2500000000 : ℝ)^8287 ≤ (1315706791893/10000000000000 : ℝ)^6239 := by
    have hnat : (542981351 : ℕ)^8287*10000000000000^6239 ≤ 1315706791893^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542981351 2500000000 1315706791893 10000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688492723/5000000000 : ℝ)^8287 ≤ (43861770498199/100000000000000 : ℝ)^6239 := by
    have hnat : (2688492723 : ℕ)^8287*100000000000000^6239 ≤ 43861770498199^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688492723 5000000000 43861770498199 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295507779/10000000000 : ℝ), (-542981351/2500000000 : ℝ), (2688492723/5000000000 : ℝ)] ![(21490580789189/50000000000000 : ℝ), (1315706791893/10000000000000 : ℝ), (43861770498199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295507779/10000000000 : ℝ)|^8287 ≤ (21490580789189/50000000000000 : ℝ)^6239
        have hw : |(5295507779/10000000000 : ℝ)|=(5295507779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-542981351/2500000000 : ℝ)|^8287 ≤ (1315706791893/10000000000000 : ℝ)^6239
        have hw : |(-542981351/2500000000 : ℝ)|=(542981351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688492723/5000000000 : ℝ)|^8287 ≤ (43861770498199/100000000000000 : ℝ)^6239
        have hw : |(2688492723/5000000000 : ℝ)|=(2688492723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_2 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295507363/10000000000 : ℝ)*x 0 + (5376985941/10000000000 : ℝ)*x 1 + (-1085962647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295507363/10000000000 : ℝ)^8287 ≤ (21490578546773/50000000000000 : ℝ)^6239 := by
    have hnat : (5295507363 : ℕ)^8287*50000000000000^6239 ≤ 21490578546773^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295507363 10000000000 21490578546773 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376985941/10000000000 : ℝ)^8287 ≤ (43861775861533/100000000000000 : ℝ)^6239 := by
    have hnat : (5376985941 : ℕ)^8287*100000000000000^6239 ≤ 43861775861533^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376985941 10000000000 43861775861533 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085962647/5000000000 : ℝ)^8287 ≤ (3289266758459/25000000000000 : ℝ)^6239 := by
    have hnat : (1085962647 : ℕ)^8287*25000000000000^6239 ≤ 3289266758459^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085962647 5000000000 3289266758459 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295507363/10000000000 : ℝ), (5376985941/10000000000 : ℝ), (-1085962647/5000000000 : ℝ)] ![(21490578546773/50000000000000 : ℝ), (43861775861533/100000000000000 : ℝ), (3289266758459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295507363/10000000000 : ℝ)|^8287 ≤ (21490578546773/50000000000000 : ℝ)^6239
        have hw : |(5295507363/10000000000 : ℝ)|=(5295507363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376985941/10000000000 : ℝ)|^8287 ≤ (43861775861533/100000000000000 : ℝ)^6239
        have hw : |(5376985941/10000000000 : ℝ)|=(5376985941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1085962647/5000000000 : ℝ)|^8287 ≤ (3289266758459/25000000000000 : ℝ)^6239
        have hw : |(-1085962647/5000000000 : ℝ)|=(1085962647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_3 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4479554669/10000000000 : ℝ)*x 0 + (4319587681/10000000000 : ℝ)*x 1 + (2159793553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4479554669/10000000000 : ℝ)^8287 ≤ (17207587431081/50000000000000 : ℝ)^6239 := by
    have hnat : (4479554669 : ℕ)^8287*50000000000000^6239 ≤ 17207587431081^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479554669 10000000000 17207587431081 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4319587681/10000000000 : ℝ)^8287 ≤ (1639620772961/5000000000000 : ℝ)^6239 := by
    have hnat : (4319587681 : ℕ)^8287*5000000000000^6239 ≤ 1639620772961^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319587681 10000000000 1639620772961 5000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2159793553/5000000000 : ℝ)^8287 ≤ (16396204830589/50000000000000 : ℝ)^6239 := by
    have hnat : (2159793553 : ℕ)^8287*50000000000000^6239 ≤ 16396204830589^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159793553 5000000000 16396204830589 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4479554669/10000000000 : ℝ), (4319587681/10000000000 : ℝ), (2159793553/5000000000 : ℝ)] ![(17207587431081/50000000000000 : ℝ), (1639620772961/5000000000000 : ℝ), (16396204830589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4479554669/10000000000 : ℝ)|^8287 ≤ (17207587431081/50000000000000 : ℝ)^6239
        have hw : |(4479554669/10000000000 : ℝ)|=(4479554669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4319587681/10000000000 : ℝ)|^8287 ≤ (1639620772961/5000000000000 : ℝ)^6239
        have hw : |(4319587681/10000000000 : ℝ)|=(4319587681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2159793553/5000000000 : ℝ)|^8287 ≤ (16396204830589/50000000000000 : ℝ)^6239
        have hw : |(2159793553/5000000000 : ℝ)|=(2159793553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_4 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-144996761/625000000 : ℝ)*x 0 + (2640247511/5000000000 : ℝ)*x 1 + (5280494751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (144996761/625000000 : ℝ)^8287 ≤ (8975768447/62500000000 : ℝ)^6239 := by
    have hnat : (144996761 : ℕ)^8287*62500000000^6239 ≤ 8975768447^6239*625000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144996761 625000000 8975768447 62500000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640247511/5000000000 : ℝ)^8287 ≤ (21409693348281/50000000000000 : ℝ)^6239 := by
    have hnat : (2640247511 : ℕ)^8287*50000000000000^6239 ≤ 21409693348281^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640247511 5000000000 21409693348281 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280494751/10000000000 : ℝ)^8287 ≤ (21409691888837/50000000000000 : ℝ)^6239 := by
    have hnat : (5280494751 : ℕ)^8287*50000000000000^6239 ≤ 21409691888837^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280494751 10000000000 21409691888837 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-144996761/625000000 : ℝ), (2640247511/5000000000 : ℝ), (5280494751/10000000000 : ℝ)] ![(8975768447/62500000000 : ℝ), (21409693348281/50000000000000 : ℝ), (21409691888837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-144996761/625000000 : ℝ)|^8287 ≤ (8975768447/62500000000 : ℝ)^6239
        have hw : |(-144996761/625000000 : ℝ)|=(144996761/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640247511/5000000000 : ℝ)|^8287 ≤ (21409693348281/50000000000000 : ℝ)^6239
        have hw : |(2640247511/5000000000 : ℝ)|=(2640247511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280494751/10000000000 : ℝ)|^8287 ≤ (21409691888837/50000000000000 : ℝ)^6239
        have hw : |(5280494751/10000000000 : ℝ)|=(5280494751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_5 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340938049/2500000000 : ℝ)*x 0 + (-220973611/1000000000 : ℝ)*x 1 + (5280494741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340938049/2500000000 : ℝ)^8287 ≤ (21859222970591/50000000000000 : ℝ)^6239 := by
    have hnat : (1340938049 : ℕ)^8287*50000000000000^6239 ≤ 21859222970591^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340938049 2500000000 21859222970591 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220973611/1000000000 : ℝ)^8287 ≤ (1682771296549/12500000000000 : ℝ)^6239 := by
    have hnat : (220973611 : ℕ)^8287*12500000000000^6239 ≤ 1682771296549^6239*1000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220973611 1000000000 1682771296549 12500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280494741/10000000000 : ℝ)^8287 ≤ (21409691834983/50000000000000 : ℝ)^6239 := by
    have hnat : (5280494741 : ℕ)^8287*50000000000000^6239 ≤ 21409691834983^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280494741 10000000000 21409691834983 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340938049/2500000000 : ℝ), (-220973611/1000000000 : ℝ), (5280494741/10000000000 : ℝ)] ![(21859222970591/50000000000000 : ℝ), (1682771296549/12500000000000 : ℝ), (21409691834983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340938049/2500000000 : ℝ)|^8287 ≤ (21859222970591/50000000000000 : ℝ)^6239
        have hw : |(1340938049/2500000000 : ℝ)|=(1340938049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220973611/1000000000 : ℝ)|^8287 ≤ (1682771296549/12500000000000 : ℝ)^6239
        have hw : |(-220973611/1000000000 : ℝ)|=(220973611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280494741/10000000000 : ℝ)|^8287 ≤ (21409691834983/50000000000000 : ℝ)^6239
        have hw : |(5280494741/10000000000 : ℝ)|=(5280494741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_6 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681876023/5000000000 : ℝ)*x 0 + (528049537/1000000000 : ℝ)*x 1 + (-88389419/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681876023/5000000000 : ℝ)^8287 ≤ (43718444317243/100000000000000 : ℝ)^6239 := by
    have hnat : (2681876023 : ℕ)^8287*100000000000000^6239 ≤ 43718444317243^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681876023 5000000000 43718444317243 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528049537/1000000000 : ℝ)^8287 ≤ (21409695222401/50000000000000 : ℝ)^6239 := by
    have hnat : (528049537 : ℕ)^8287*50000000000000^6239 ≤ 21409695222401^6239*1000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528049537 1000000000 21409695222401 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88389419/400000000 : ℝ)^8287 ≤ (13462165233959/100000000000000 : ℝ)^6239 := by
    have hnat : (88389419 : ℕ)^8287*100000000000000^6239 ≤ 13462165233959^6239*400000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88389419 400000000 13462165233959 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681876023/5000000000 : ℝ), (528049537/1000000000 : ℝ), (-88389419/400000000 : ℝ)] ![(43718444317243/100000000000000 : ℝ), (21409695222401/50000000000000 : ℝ), (13462165233959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681876023/5000000000 : ℝ)|^8287 ≤ (43718444317243/100000000000000 : ℝ)^6239
        have hw : |(2681876023/5000000000 : ℝ)|=(2681876023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528049537/1000000000 : ℝ)|^8287 ≤ (21409695222401/50000000000000 : ℝ)^6239
        have hw : |(528049537/1000000000 : ℝ)|=(528049537/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88389419/400000000 : ℝ)|^8287 ≤ (13462165233959/100000000000000 : ℝ)^6239
        have hw : |(-88389419/400000000 : ℝ)|=(88389419/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_7 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4263067989/10000000000 : ℝ)*x 0 + (4427809711/10000000000 : ℝ)*x 1 + (4427809303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4263067989/10000000000 : ℝ)^8287 ≤ (644474476761/2000000000000 : ℝ)^6239 := by
    have hnat : (4263067989 : ℕ)^8287*2000000000000^6239 ≤ 644474476761^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4263067989 10000000000 644474476761 2000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4427809711/10000000000 : ℝ)^8287 ≤ (33888140148191/100000000000000 : ℝ)^6239 := by
    have hnat : (4427809711 : ℕ)^8287*100000000000000^6239 ≤ 33888140148191^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427809711 10000000000 33888140148191 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4427809303/10000000000 : ℝ)^8287 ≤ (33888136000549/100000000000000 : ℝ)^6239 := by
    have hnat : (4427809303 : ℕ)^8287*100000000000000^6239 ≤ 33888136000549^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427809303 10000000000 33888136000549 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4263067989/10000000000 : ℝ), (4427809711/10000000000 : ℝ), (4427809303/10000000000 : ℝ)] ![(644474476761/2000000000000 : ℝ), (33888140148191/100000000000000 : ℝ), (33888136000549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4263067989/10000000000 : ℝ)|^8287 ≤ (644474476761/2000000000000 : ℝ)^6239
        have hw : |(4263067989/10000000000 : ℝ)|=(4263067989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4427809711/10000000000 : ℝ)|^8287 ≤ (33888140148191/100000000000000 : ℝ)^6239
        have hw : |(4427809711/10000000000 : ℝ)|=(4427809711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4427809303/10000000000 : ℝ)|^8287 ≤ (33888136000549/100000000000000 : ℝ)^6239
        have hw : |(4427809303/10000000000 : ℝ)|=(4427809303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_8 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1132985369/5000000000 : ℝ)*x 0 + (2607482739/5000000000 : ℝ)*x 1 + (336661869/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1132985369/5000000000 : ℝ)^8287 ≤ (695955607503/5000000000000 : ℝ)^6239 := by
    have hnat : (1132985369 : ℕ)^8287*5000000000000^6239 ≤ 695955607503^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132985369 5000000000 695955607503 5000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607482739/5000000000 : ℝ)^8287 ≤ (42115022362563/100000000000000 : ℝ)^6239 := by
    have hnat : (2607482739 : ℕ)^8287*100000000000000^6239 ≤ 42115022362563^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607482739 5000000000 42115022362563 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336661869/625000000 : ℝ)^8287 ≤ (43965865473041/100000000000000 : ℝ)^6239 := by
    have hnat : (336661869 : ℕ)^8287*100000000000000^6239 ≤ 43965865473041^6239*625000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336661869 625000000 43965865473041 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1132985369/5000000000 : ℝ), (2607482739/5000000000 : ℝ), (336661869/625000000 : ℝ)] ![(695955607503/5000000000000 : ℝ), (42115022362563/100000000000000 : ℝ), (43965865473041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1132985369/5000000000 : ℝ)|^8287 ≤ (695955607503/5000000000000 : ℝ)^6239
        have hw : |(-1132985369/5000000000 : ℝ)|=(1132985369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607482739/5000000000 : ℝ)|^8287 ≤ (42115022362563/100000000000000 : ℝ)^6239
        have hw : |(2607482739/5000000000 : ℝ)|=(2607482739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336661869/625000000 : ℝ)|^8287 ≤ (43965865473041/100000000000000 : ℝ)^6239
        have hw : |(336661869/625000000 : ℝ)|=(336661869/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_9 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644355597/5000000000 : ℝ)*x 0 + (-2168091313/10000000000 : ℝ)*x 1 + (2693295129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644355597/5000000000 : ℝ)^8287 ≤ (21453952036781/50000000000000 : ℝ)^6239 := by
    have hnat : (2644355597 : ℕ)^8287*50000000000000^6239 ≤ 21453952036781^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644355597 5000000000 21453952036781 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2168091313/10000000000 : ℝ)^8287 ≤ (13126226590061/100000000000000 : ℝ)^6239 := by
    have hnat : (2168091313 : ℕ)^8287*100000000000000^6239 ≤ 13126226590061^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168091313 10000000000 13126226590061 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693295129/5000000000 : ℝ)^8287 ≤ (8793173862177/20000000000000 : ℝ)^6239 := by
    have hnat : (2693295129 : ℕ)^8287*20000000000000^6239 ≤ 8793173862177^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693295129 5000000000 8793173862177 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644355597/5000000000 : ℝ), (-2168091313/10000000000 : ℝ), (2693295129/5000000000 : ℝ)] ![(21453952036781/50000000000000 : ℝ), (13126226590061/100000000000000 : ℝ), (8793173862177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644355597/5000000000 : ℝ)|^8287 ≤ (21453952036781/50000000000000 : ℝ)^6239
        have hw : |(2644355597/5000000000 : ℝ)|=(2644355597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2168091313/10000000000 : ℝ)|^8287 ≤ (13126226590061/100000000000000 : ℝ)^6239
        have hw : |(-2168091313/10000000000 : ℝ)|=(2168091313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693295129/5000000000 : ℝ)|^8287 ≤ (8793173862177/20000000000000 : ℝ)^6239
        have hw : |(2693295129/5000000000 : ℝ)|=(2693295129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_10 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322177803/2500000000 : ℝ)*x 0 + (5386589837/10000000000 : ℝ)*x 1 + (-2168091859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322177803/2500000000 : ℝ)^8287 ≤ (2681744016721/6250000000000 : ℝ)^6239 := by
    have hnat : (1322177803 : ℕ)^8287*6250000000000^6239 ≤ 2681744016721^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322177803 2500000000 2681744016721 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386589837/10000000000 : ℝ)^8287 ≤ (4396586474667/10000000000000 : ℝ)^6239 := by
    have hnat : (5386589837 : ℕ)^8287*10000000000000^6239 ≤ 4396586474667^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386589837 10000000000 4396586474667 10000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168091859/10000000000 : ℝ)^8287 ≤ (13126230980797/100000000000000 : ℝ)^6239 := by
    have hnat : (2168091859 : ℕ)^8287*100000000000000^6239 ≤ 13126230980797^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168091859 10000000000 13126230980797 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322177803/2500000000 : ℝ), (5386589837/10000000000 : ℝ), (-2168091859/10000000000 : ℝ)] ![(2681744016721/6250000000000 : ℝ), (4396586474667/10000000000000 : ℝ), (13126230980797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322177803/2500000000 : ℝ)|^8287 ≤ (2681744016721/6250000000000 : ℝ)^6239
        have hw : |(1322177803/2500000000 : ℝ)|=(1322177803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386589837/10000000000 : ℝ)|^8287 ≤ (4396586474667/10000000000000 : ℝ)^6239
        have hw : |(5386589837/10000000000 : ℝ)|=(5386589837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2168091859/10000000000 : ℝ)|^8287 ≤ (13126230980797/100000000000000 : ℝ)^6239
        have hw : |(-2168091859/10000000000 : ℝ)|=(2168091859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_11 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4500830187/10000000000 : ℝ)*x 0 + (4308809041/10000000000 : ℝ)*x 1 + (1077202287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4500830187/10000000000 : ℝ)^8287 ≤ (34632452828637/100000000000000 : ℝ)^6239 := by
    have hnat : (4500830187 : ℕ)^8287*100000000000000^6239 ≤ 34632452828637^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500830187 10000000000 34632452828637 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4308809041/10000000000 : ℝ)^8287 ≤ (8170943259693/25000000000000 : ℝ)^6239 := by
    have hnat : (4308809041 : ℕ)^8287*25000000000000^6239 ≤ 8170943259693^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308809041 10000000000 8170943259693 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077202287/2500000000 : ℝ)^8287 ≤ (32683774116827/100000000000000 : ℝ)^6239 := by
    have hnat : (1077202287 : ℕ)^8287*100000000000000^6239 ≤ 32683774116827^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077202287 2500000000 32683774116827 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4500830187/10000000000 : ℝ), (4308809041/10000000000 : ℝ), (1077202287/2500000000 : ℝ)] ![(34632452828637/100000000000000 : ℝ), (8170943259693/25000000000000 : ℝ), (32683774116827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4500830187/10000000000 : ℝ)|^8287 ≤ (34632452828637/100000000000000 : ℝ)^6239
        have hw : |(4500830187/10000000000 : ℝ)|=(4500830187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4308809041/10000000000 : ℝ)|^8287 ≤ (8170943259693/25000000000000 : ℝ)^6239
        have hw : |(4308809041/10000000000 : ℝ)|=(4308809041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077202287/2500000000 : ℝ)|^8287 ≤ (32683774116827/100000000000000 : ℝ)^6239
        have hw : |(1077202287/2500000000 : ℝ)|=(1077202287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_12 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115878061/10000000000 : ℝ)*x 0 + (1088240293/2000000000 : ℝ)*x 1 + (2636239653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115878061/10000000000 : ℝ)^8287 ≤ (1588501880231/12500000000000 : ℝ)^6239 := by
    have hnat : (2115878061 : ℕ)^8287*12500000000000^6239 ≤ 1588501880231^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115878061 10000000000 1588501880231 12500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088240293/2000000000 : ℝ)^8287 ≤ (44558912449357/100000000000000 : ℝ)^6239 := by
    have hnat : (1088240293 : ℕ)^8287*100000000000000^6239 ≤ 44558912449357^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088240293 2000000000 44558912449357 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636239653/5000000000 : ℝ)^8287 ≤ (42733072501039/100000000000000 : ℝ)^6239 := by
    have hnat : (2636239653 : ℕ)^8287*100000000000000^6239 ≤ 42733072501039^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636239653 5000000000 42733072501039 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115878061/10000000000 : ℝ), (1088240293/2000000000 : ℝ), (2636239653/5000000000 : ℝ)] ![(1588501880231/12500000000000 : ℝ), (44558912449357/100000000000000 : ℝ), (42733072501039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115878061/10000000000 : ℝ)|^8287 ≤ (1588501880231/12500000000000 : ℝ)^6239
        have hw : |(-2115878061/10000000000 : ℝ)|=(2115878061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088240293/2000000000 : ℝ)|^8287 ≤ (44558912449357/100000000000000 : ℝ)^6239
        have hw : |(1088240293/2000000000 : ℝ)|=(1088240293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636239653/5000000000 : ℝ)|^8287 ≤ (42733072501039/100000000000000 : ℝ)^6239
        have hw : |(2636239653/5000000000 : ℝ)|=(2636239653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_13 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684709199/5000000000 : ℝ)*x 0 + (-2212818729/10000000000 : ℝ)*x 1 + (1054495981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684709199/5000000000 : ℝ)^8287 ≤ (21889900169071/50000000000000 : ℝ)^6239 := by
    have hnat : (2684709199 : ℕ)^8287*50000000000000^6239 ≤ 21889900169071^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684709199 5000000000 21889900169071 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212818729/10000000000 : ℝ)^8287 ≤ (13487120700933/100000000000000 : ℝ)^6239 := by
    have hnat : (2212818729 : ℕ)^8287*100000000000000^6239 ≤ 13487120700933^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212818729 10000000000 13487120700933 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054495981/2000000000 : ℝ)^8287 ≤ (8546615789907/20000000000000 : ℝ)^6239 := by
    have hnat : (1054495981 : ℕ)^8287*20000000000000^6239 ≤ 8546615789907^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054495981 2000000000 8546615789907 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684709199/5000000000 : ℝ), (-2212818729/10000000000 : ℝ), (1054495981/2000000000 : ℝ)] ![(21889900169071/50000000000000 : ℝ), (13487120700933/100000000000000 : ℝ), (8546615789907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684709199/5000000000 : ℝ)|^8287 ≤ (21889900169071/50000000000000 : ℝ)^6239
        have hw : |(2684709199/5000000000 : ℝ)|=(2684709199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2212818729/10000000000 : ℝ)|^8287 ≤ (13487120700933/100000000000000 : ℝ)^6239
        have hw : |(-2212818729/10000000000 : ℝ)|=(2212818729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054495981/2000000000 : ℝ)|^8287 ≤ (8546615789907/20000000000000 : ℝ)^6239
        have hw : |(1054495981/2000000000 : ℝ)|=(1054495981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_14 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369418543/10000000000 : ℝ)*x 0 + (131811997/250000000 : ℝ)*x 1 + (-2212818569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369418543/10000000000 : ℝ)^8287 ≤ (21889900954247/50000000000000 : ℝ)^6239 := by
    have hnat : (5369418543 : ℕ)^8287*50000000000000^6239 ≤ 21889900954247^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369418543 10000000000 21889900954247 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131811997/250000000 : ℝ)^8287 ≤ (42733078680399/100000000000000 : ℝ)^6239 := by
    have hnat : (131811997 : ℕ)^8287*100000000000000^6239 ≤ 42733078680399^6239*250000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131811997 250000000 42733078680399 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212818569/10000000000 : ℝ)^8287 ≤ (13487119405617/100000000000000 : ℝ)^6239 := by
    have hnat : (2212818569 : ℕ)^8287*100000000000000^6239 ≤ 13487119405617^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212818569 10000000000 13487119405617 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369418543/10000000000 : ℝ), (131811997/250000000 : ℝ), (-2212818569/10000000000 : ℝ)] ![(21889900954247/50000000000000 : ℝ), (42733078680399/100000000000000 : ℝ), (13487119405617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369418543/10000000000 : ℝ)|^8287 ≤ (21889900954247/50000000000000 : ℝ)^6239
        have hw : |(5369418543/10000000000 : ℝ)|=(5369418543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131811997/250000000 : ℝ)|^8287 ≤ (42733078680399/100000000000000 : ℝ)^6239
        have hw : |(131811997/250000000 : ℝ)|=(131811997/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2212818569/10000000000 : ℝ)|^8287 ≤ (13487119405617/100000000000000 : ℝ)^6239
        have hw : |(-2212818569/10000000000 : ℝ)|=(2212818569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_box_15 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061213153/2500000000 : ℝ)*x 0 + (2218397367/5000000000 : ℝ)*x 1 + (2218397869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061213153/2500000000 : ℝ)^8287 ≤ (8010242235809/25000000000000 : ℝ)^6239 := by
    have hnat : (1061213153 : ℕ)^8287*25000000000000^6239 ≤ 8010242235809^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061213153 2500000000 8010242235809 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2218397367/5000000000 : ℝ)^8287 ≤ (33979510413599/100000000000000 : ℝ)^6239 := by
    have hnat : (2218397367 : ℕ)^8287*100000000000000^6239 ≤ 33979510413599^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218397367 5000000000 33979510413599 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2218397869/5000000000 : ℝ)^8287 ≤ (33979520626847/100000000000000 : ℝ)^6239 := by
    have hnat : (2218397869 : ℕ)^8287*100000000000000^6239 ≤ 33979520626847^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218397869 5000000000 33979520626847 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061213153/2500000000 : ℝ), (2218397367/5000000000 : ℝ), (2218397869/5000000000 : ℝ)] ![(8010242235809/25000000000000 : ℝ), (33979510413599/100000000000000 : ℝ), (33979520626847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061213153/2500000000 : ℝ)|^8287 ≤ (8010242235809/25000000000000 : ℝ)^6239
        have hw : |(1061213153/2500000000 : ℝ)|=(1061213153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2218397367/5000000000 : ℝ)|^8287 ≤ (33979510413599/100000000000000 : ℝ)^6239
        have hw : |(2218397367/5000000000 : ℝ)|=(2218397367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2218397869/5000000000 : ℝ)|^8287 ≤ (33979520626847/100000000000000 : ℝ)^6239
        have hw : |(2218397869/5000000000 : ℝ)|=(2218397869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1094_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31113/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29631/50000 : ℝ) ∧ (3983/5000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10377/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1129/10000 : ℝ) ^ (4143/1024 : ℝ) ≤ (3674818621939473/25000000000000000000 : ℝ) := by
    have hpowers : (1129/10000 : ℝ)^4143 ≤ (3674818621939473/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1129 : ℕ)^4143*25000000000000000000^1024 ≤ 3674818621939473^1024*10000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1129 10000 3674818621939473 25000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1129/10000 : ℝ)) (X := (3674818621939473/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (701/5000 : ℝ) ^ (4143/1024 : ℝ) ≤ (7060884658271387/20000000000000000000 : ℝ) := by
    have hpowers : (701/5000 : ℝ)^4143 ≤ (7060884658271387/20000000000000000000 : ℝ)^1024 := by
      have hnat : (701 : ℕ)^4143*20000000000000000000^1024 ≤ 7060884658271387^1024*5000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 5000 7060884658271387 20000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/5000 : ℝ)) (X := (7060884658271387/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503674818621939473/12500000000000000000 : ℝ) ≤ (1000072654557949/1000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (12503674818621939473/12500000000000000000 : ℝ)^1024 ≤ (1000072654557949/1000000000000000 : ℝ)^4143 := by
      have hnat : (12503674818621939473 : ℕ)^1024*1000000000000000^4143 ≤ 1000072654557949^4143*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503674818621939473 12500000000000000000 1000072654557949 1000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000072654557949/1000000000000000 : ℝ)) (X := (12503674818621939473/12500000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050003697779114827/100000000000000000000 : ℝ) ≤ (10001235678291409/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (100050003697779114827/100000000000000000000 : ℝ)^1024 ≤ (10001235678291409/10000000000000000 : ℝ)^4143 := by
      have hnat : (100050003697779114827 : ℕ)^1024*10000000000000000^4143 ≤ 10001235678291409^4143*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050003697779114827 100000000000000000000 10001235678291409 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001235678291409/10000000000000000 : ℝ)) (X := (100050003697779114827/100000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007060884658271387/10000000000000000000 : ℝ) ≤ (156277262671927/156250000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (10007060884658271387/10000000000000000000 : ℝ)^1024 ≤ (156277262671927/156250000000000 : ℝ)^4143 := by
      have hnat : (10007060884658271387 : ℕ)^1024*156250000000000^4143 ≤ 156277262671927^4143*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007060884658271387 10000000000000000000 156277262671927 156250000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156277262671927/156250000000000 : ℝ)) (X := (10007060884658271387/10000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3674818621939473/25000000000000000000 : ℝ) ≤ ((17493902085126203/17500000000000000 : ℝ)+2*(13054684921/7000000000000 : ℝ)*(1129/10000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (17493902085126203/17500000000000000 : ℝ)+2*(13054684921/7000000000000 : ℝ)*(1129/10000 : ℝ)=(1000072654557949/1000000000000000 : ℝ) by norm_num, show 1+2*(3674818621939473/25000000000000000000 : ℝ)=(12503674818621939473/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7060884658271387/20000000000000000000 : ℝ)+(3674818621939473/25000000000000000000 : ℝ) ≤ ((17493902085126203/17500000000000000 : ℝ)+(13054684921/7000000000000 : ℝ)*((701/5000 : ℝ)+(1129/10000 : ℝ)))^(4143/1024 : ℝ) := by
    rw [show (17493902085126203/17500000000000000 : ℝ)+(13054684921/7000000000000 : ℝ)*((701/5000 : ℝ)+(1129/10000 : ℝ))=(10001235678291409/10000000000000000 : ℝ) by norm_num, show 1+(7060884658271387/20000000000000000000 : ℝ)+(3674818621939473/25000000000000000000 : ℝ)=(100050003697779114827/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7060884658271387/20000000000000000000 : ℝ) ≤ ((17493902085126203/17500000000000000 : ℝ)+2*(13054684921/7000000000000 : ℝ)*(701/5000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (17493902085126203/17500000000000000 : ℝ)+2*(13054684921/7000000000000 : ℝ)*(701/5000 : ℝ)=(156277262671927/156250000000000 : ℝ) by norm_num, show 1+2*(7060884658271387/20000000000000000000 : ℝ)=(10007060884658271387/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17493902085126203/17500000000000000 : ℝ)*(X 1 0+X 2 0)+(13054684921/7000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (17493902085126203/17500000000000000 : ℝ)) (alpha := (13054684921/7000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17493902085126203/17500000000000000 : ℝ)*(X 0 1+X 2 1)+(13054684921/7000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (17493902085126203/17500000000000000 : ℝ)) (alpha := (13054684921/7000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17493902085126203/17500000000000000 : ℝ)*(X 0 2+X 1 2)+(13054684921/7000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (17493902085126203/17500000000000000 : ℝ)) (alpha := (13054684921/7000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2061551277/10000000000 : ℝ)*X 0 0+(5376985503/10000000000 : ℝ)*X 0 1+(2688492763/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295507779/10000000000 : ℝ)*X 1 0+(-542981351/2500000000 : ℝ)*X 1 1+(2688492723/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295507363/10000000000 : ℝ)*X 2 0+(5376985941/10000000000 : ℝ)*X 2 1+(-1085962647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4479554669/10000000000 : ℝ)*X 0 0+(4319587681/10000000000 : ℝ)*X 0 1+(2159793553/5000000000 : ℝ)*X 0 2+(4479554669/10000000000 : ℝ)*X 1 0+(4319587681/10000000000 : ℝ)*X 1 1+(2159793553/5000000000 : ℝ)*X 1 2+(4479554669/10000000000 : ℝ)*X 2 0+(4319587681/10000000000 : ℝ)*X 2 1+(2159793553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-144996761/625000000 : ℝ)*X 0 0+(2640247511/5000000000 : ℝ)*X 0 1+(5280494751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1340938049/2500000000 : ℝ)*X 1 0+(-220973611/1000000000 : ℝ)*X 1 1+(5280494741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681876023/5000000000 : ℝ)*X 2 0+(528049537/1000000000 : ℝ)*X 2 1+(-88389419/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4263067989/10000000000 : ℝ)*X 0 0+(4427809711/10000000000 : ℝ)*X 0 1+(4427809303/10000000000 : ℝ)*X 0 2+(4263067989/10000000000 : ℝ)*X 1 0+(4427809711/10000000000 : ℝ)*X 1 1+(4427809303/10000000000 : ℝ)*X 1 2+(4263067989/10000000000 : ℝ)*X 2 0+(4427809711/10000000000 : ℝ)*X 2 1+(4427809303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1132985369/5000000000 : ℝ)*X 0 0+(2607482739/5000000000 : ℝ)*X 0 1+(336661869/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644355597/5000000000 : ℝ)*X 1 0+(-2168091313/10000000000 : ℝ)*X 1 1+(2693295129/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322177803/2500000000 : ℝ)*X 2 0+(5386589837/10000000000 : ℝ)*X 2 1+(-2168091859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4500830187/10000000000 : ℝ)*X 0 0+(4308809041/10000000000 : ℝ)*X 0 1+(1077202287/2500000000 : ℝ)*X 0 2+(4500830187/10000000000 : ℝ)*X 1 0+(4308809041/10000000000 : ℝ)*X 1 1+(1077202287/2500000000 : ℝ)*X 1 2+(4500830187/10000000000 : ℝ)*X 2 0+(4308809041/10000000000 : ℝ)*X 2 1+(1077202287/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2115878061/10000000000 : ℝ)*X 0 0+(1088240293/2000000000 : ℝ)*X 0 1+(2636239653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684709199/5000000000 : ℝ)*X 1 0+(-2212818729/10000000000 : ℝ)*X 1 1+(1054495981/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369418543/10000000000 : ℝ)*X 2 0+(131811997/250000000 : ℝ)*X 2 1+(-2212818569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1061213153/2500000000 : ℝ)*X 0 0+(2218397367/5000000000 : ℝ)*X 0 1+(2218397869/5000000000 : ℝ)*X 0 2+(1061213153/2500000000 : ℝ)*X 1 0+(2218397367/5000000000 : ℝ)*X 1 1+(2218397869/5000000000 : ℝ)*X 1 2+(1061213153/2500000000 : ℝ)*X 2 0+(2218397367/5000000000 : ℝ)*X 2 1+(2218397869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31113/50000 : ℝ) ≤ (-68057440574297121930214196571/109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35284741/100000000000000 : ℝ)*(lower2) + (220974119/100000000000000 : ℝ)*(upper4) + (19286481/50000000000000 : ℝ)*(upper5) + (485015560114423/12500000000000 : ℝ)*(major0) + (485015560114423/12500000000000 : ℝ)*(major1) + (485015560114423/12500000000000 : ℝ)*(major2) + (21395516687/100000000000000 : ℝ)*(sp1) + (315107143/50000000000000 : ℝ)*(sp3) + (5168761962254927/100000000000000 : ℝ)*(sp4) + (5168759538205087/100000000000000 : ℝ)*(sp5) + (1033689910129599/20000000000000 : ℝ)*(sp6) + (1306104356558669/50000000000000 : ℝ)*(sp7) + (18971466847/100000000000000 : ℝ)*(sp8) + (331383073779/100000000000000 : ℝ)*(sp14) + (326526167916453/12500000000000 : ℝ)*(f.failure) + (2584390466860887/50000000000000 : ℝ)*(f.sum) + (621508448091/87500000000000000000000000 : ℝ)*base65 + (514559599354767/31250000000000000000000000000 : ℝ)*base67 + (553708622761017/31250000000000000000000000000 : ℝ)*base69 + (849895146323517/31250000000000000000000000000 : ℝ)*base71 + (653643365859/87500000000000000000000000 : ℝ)*base74 + (495465372636017/31250000000000000000000000000 : ℝ)*base75 + (347416941886017/31250000000000000000000000000 : ℝ)*base77 + (440016836542267/31250000000000000000000000000 : ℝ)*base79 + (474127918559/87500000000000000000000000 : ℝ)*base82 + (8622761/1250000000000000000000 : ℝ)*base89 + (8622761/1250000000000000000000 : ℝ)*base91 + (8622761/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29631/50000 : ℝ) ≤ (16205061272849050936927338603/27343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (82830223/100000000000000 : ℝ)*(lower0) + (2078597/25000000000000 : ℝ)*(upper1) + (88089/3125000000000 : ℝ)*(upper2) + (48258173/50000000000000 : ℝ)*(upper3) + (13578587/50000000000000 : ℝ)*(lower5) + (492935625967769/12500000000000 : ℝ)*(major0) + (492935625967769/12500000000000 : ℝ)*(major1) + (492935625967769/12500000000000 : ℝ)*(major2) + (5212349835351923/100000000000000 : ℝ)*(sp0) + (260610729492843/5000000000000 : ℝ)*(sp1) + (1042466388940959/20000000000000 : ℝ)*(sp2) + (2654865438771183/100000000000000 : ℝ)*(sp3) + (2236330891/12500000000000 : ℝ)*(sp6) + (135245495063/100000000000000 : ℝ)*(sp9) + (2654865438771183/100000000000000 : ℝ)*(f.failure) + (5212349835351923/100000000000000 : ℝ)*(f.sum) + (50035430481/10937500000000000000000000 : ℝ)*base65 + (347137494049801/31250000000000000000000000000 : ℝ)*base67 + (23585493924801/31250000000000000000000000000 : ℝ)*base69 + (226609878518551/31250000000000000000000000000 : ℝ)*base71 + (261085922199/43750000000000000000000000 : ℝ)*base73 + (426745202799801/31250000000000000000000000000 : ℝ)*base75 + (430622993799801/31250000000000000000000000000 : ℝ)*base77 + (942640238237301/31250000000000000000000000000 : ℝ)*base79 + (93511250997/5468750000000000000000000 : ℝ)*base82 + (14987771/10000000000000000000000 : ℝ)*base89 + (14987771/10000000000000000000000 : ℝ)*base91 + (14987771/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (3983/5000 : ℝ) ≤ (49788989335132115321805139227/62500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126737741/100000000000000 : ℝ)*(upper0) + (9787569/50000000000000 : ℝ)*(lower1) + (24556877/20000000000000 : ℝ)*(upper2) + (357492833/100000000000000 : ℝ)*(lower5) + (2205807506758093/50000000000000 : ℝ)*(major0) + (2205807506758093/50000000000000 : ℝ)*(major1) + (2205807506758093/50000000000000 : ℝ)*(major2) + (1717717009/100000000000000 : ℝ)*(sp0) + (196087240793/100000000000000 : ℝ)*(sp1) + (8259769697/10000000000000 : ℝ)*(sp3) + (5826650406873333/100000000000000 : ℝ)*(sp8) + (1456614009337387/25000000000000 : ℝ)*(sp9) + (2913326062295171/50000000000000 : ℝ)*(sp10) + (74248529427491/2500000000000 : ℝ)*(sp11) + (297002377479661/10000000000000 : ℝ)*(f.failure) + (2913326062295171/50000000000000 : ℝ)*(f.sum) + (11535078163/3125000000000000000000000 : ℝ)*base65 + (1229769591231197/125000000000000000000000000000 : ℝ)*base67 + (1199866241856197/125000000000000000000000000000 : ℝ)*base69 + (1859849071481197/125000000000000000000000000000 : ℝ)*base71 + (315345511529/25000000000000000000000000 : ℝ)*base73 + (2855571204856197/125000000000000000000000000000 : ℝ)*base75 + (2601568390856197/125000000000000000000000000000 : ℝ)*base77 + (2124490147106197/125000000000000000000000000000 : ℝ)*base79 + (65123484671/25000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7634543/1000000000000000000000 : ℝ)*base90 + (7634543/1000000000000000000000 : ℝ)*base92 + (7634543/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-10377/12500 : ℝ) ≤ (-45398175590545813250011764837/54687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (138885157/100000000000000 : ℝ)*(lower1) + (181666423/100000000000000 : ℝ)*(upper3) + (4477173/50000000000000 : ℝ)*(lower4) + (97944653/20000000000000 : ℝ)*(upper5) + (555791951103637/12500000000000 : ℝ)*(major0) + (555791951103637/12500000000000 : ℝ)*(major1) + (555791951103637/12500000000000 : ℝ)*(major2) + (2687963293/6250000000000 : ℝ)*(sp4) + (20933354437/12500000000000 : ℝ)*(sp6) + (410298597579/100000000000000 : ℝ)*(sp7) + (1481725204847941/25000000000000 : ℝ)*(sp12) + (1481735956701113/25000000000000 : ℝ)*(sp13) + (5926776359968957/100000000000000 : ℝ)*(sp14) + (2992988361187521/100000000000000 : ℝ)*(sp15) + (29933986597851/1000000000000 : ℝ)*(f.failure) + (1481735956701113/25000000000000 : ℝ)*(f.sum) + (1029225057717/175000000000000000000000000 : ℝ)*base66 + (119571228280223/31250000000000000000000000000 : ℝ)*base67 + (1542798668030223/31250000000000000000000000000 : ℝ)*base69 + (179677981405223/31250000000000000000000000000 : ℝ)*base71 + (640815319917/175000000000000000000000000 : ℝ)*base74 + (1503333024655223/31250000000000000000000000000 : ℝ)*base75 + (200975276061473/31250000000000000000000000000 : ℝ)*base77 + (6528563155223/31250000000000000000000000000 : ℝ)*base79 + (5927349832679/87500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (41513/100000000000000000000 : ℝ)*base90 + (41513/100000000000000000000 : ℝ)*base92 + (41513/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1094_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29631/50000 : ℝ) else (3983/5000 : ℝ) ≤ X j i ∧ X j i ≤ (10377/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1094_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1094_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29631/50000 : ℝ) else (3983/5000 : ℝ) ≤ X j i ∧ X j i ≤ (10377/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1094_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29631/50000 : ℝ) else (3983/5000 : ℝ) ≤ X j i ∧ X j i ≤ (10377/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1094_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
