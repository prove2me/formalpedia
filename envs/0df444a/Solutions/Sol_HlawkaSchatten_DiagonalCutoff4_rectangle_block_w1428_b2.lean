-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1428_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:53:37.631994+00:00
-- url     : https://prove2.me/submissions/93b9fa52-84e1-4260-adbf-4de68cf7a68e

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
theorem support_rectangle_w1428_s6_0 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1971942487/10000000000 : ℝ)*x 0 + (2704136559/5000000000 : ℝ)*x 1 + (2623440579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1971942487/10000000000 : ℝ)^1097 ≤ (187966482197/1562500000000 : ℝ)^841 := by
    have hnat : (1971942487 : ℕ)^1097*1562500000000^841 ≤ 187966482197^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971942487 10000000000 187966482197 1562500000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704136559/5000000000 : ℝ)^1097 ≤ (44854062602513/100000000000000 : ℝ)^841 := by
    have hnat : (2704136559 : ℕ)^1097*100000000000000^841 ≤ 44854062602513^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704136559 5000000000 44854062602513 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623440579/5000000000 : ℝ)^1097 ≤ (431160825159/1000000000000 : ℝ)^841 := by
    have hnat : (2623440579 : ℕ)^1097*1000000000000^841 ≤ 431160825159^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623440579 5000000000 431160825159 1000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1971942487/10000000000 : ℝ), (2704136559/5000000000 : ℝ), (2623440579/5000000000 : ℝ)] ![(187966482197/1562500000000 : ℝ), (44854062602513/100000000000000 : ℝ), (431160825159/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1971942487/10000000000 : ℝ)|^1097 ≤ (187966482197/1562500000000 : ℝ)^841
        have hw : |(-1971942487/10000000000 : ℝ)|=(1971942487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704136559/5000000000 : ℝ)|^1097 ≤ (44854062602513/100000000000000 : ℝ)^841
        have hw : |(2704136559/5000000000 : ℝ)|=(2704136559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623440579/5000000000 : ℝ)|^1097 ≤ (431160825159/1000000000000 : ℝ)^841
        have hw : |(2623440579/5000000000 : ℝ)|=(2623440579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s6_1 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347348609/10000000000 : ℝ)*x 0 + (-2054110439/10000000000 : ℝ)*x 1 + (5246881131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347348609/10000000000 : ℝ)^1097 ≤ (11049025978029/25000000000000 : ℝ)^841 := by
    have hnat : (5347348609 : ℕ)^1097*25000000000000^841 ≤ 11049025978029^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347348609 10000000000 11049025978029 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2054110439/10000000000 : ℝ)^1097 ≤ (12687813848457/100000000000000 : ℝ)^841 := by
    have hnat : (2054110439 : ℕ)^1097*100000000000000^841 ≤ 12687813848457^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054110439 10000000000 12687813848457 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246881131/10000000000 : ℝ)^1097 ≤ (43116082226491/100000000000000 : ℝ)^841 := by
    have hnat : (5246881131 : ℕ)^1097*100000000000000^841 ≤ 43116082226491^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246881131 10000000000 43116082226491 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347348609/10000000000 : ℝ), (-2054110439/10000000000 : ℝ), (5246881131/10000000000 : ℝ)] ![(11049025978029/25000000000000 : ℝ), (12687813848457/100000000000000 : ℝ), (43116082226491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347348609/10000000000 : ℝ)|^1097 ≤ (11049025978029/25000000000000 : ℝ)^841
        have hw : |(5347348609/10000000000 : ℝ)|=(5347348609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2054110439/10000000000 : ℝ)|^1097 ≤ (12687813848457/100000000000000 : ℝ)^841
        have hw : |(-2054110439/10000000000 : ℝ)|=(2054110439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246881131/10000000000 : ℝ)|^1097 ≤ (43116082226491/100000000000000 : ℝ)^841
        have hw : |(5246881131/10000000000 : ℝ)|=(5246881131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s6_2 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069469721/2000000000 : ℝ)*x 0 + (5246881193/10000000000 : ℝ)*x 1 + (-2054110361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069469721/2000000000 : ℝ)^1097 ≤ (690564122953/1562500000000 : ℝ)^841 := by
    have hnat : (1069469721 : ℕ)^1097*1562500000000^841 ≤ 690564122953^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069469721 2000000000 690564122953 1562500000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246881193/10000000000 : ℝ)^1097 ≤ (2155804144553/5000000000000 : ℝ)^841 := by
    have hnat : (5246881193 : ℕ)^1097*5000000000000^841 ≤ 2155804144553^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246881193 10000000000 2155804144553 5000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054110361/10000000000 : ℝ)^1097 ≤ (1268781322001/10000000000000 : ℝ)^841 := by
    have hnat : (2054110361 : ℕ)^1097*10000000000000^841 ≤ 1268781322001^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054110361 10000000000 1268781322001 10000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069469721/2000000000 : ℝ), (5246881193/10000000000 : ℝ), (-2054110361/10000000000 : ℝ)] ![(690564122953/1562500000000 : ℝ), (2155804144553/5000000000000 : ℝ), (1268781322001/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069469721/2000000000 : ℝ)|^1097 ≤ (690564122953/1562500000000 : ℝ)^841
        have hw : |(1069469721/2000000000 : ℝ)|=(1069469721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246881193/10000000000 : ℝ)|^1097 ≤ (2155804144553/5000000000000 : ℝ)^841
        have hw : |(5246881193/10000000000 : ℝ)|=(5246881193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054110361/10000000000 : ℝ)|^1097 ≤ (1268781322001/10000000000000 : ℝ)^841
        have hw : |(-2054110361/10000000000 : ℝ)|=(2054110361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s6_3 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4304623169/10000000000 : ℝ)*x 0 + (4133297937/10000000000 : ℝ)*x 1 + (2241157359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304623169/10000000000 : ℝ)^1097 ≤ (6660934528659/20000000000000 : ℝ)^841 := by
    have hnat : (4304623169 : ℕ)^1097*20000000000000^841 ≤ 6660934528659^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304623169 10000000000 6660934528659 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4133297937/10000000000 : ℝ)^1097 ≤ (31586216855909/100000000000000 : ℝ)^841 := by
    have hnat : (4133297937 : ℕ)^1097*100000000000000^841 ≤ 31586216855909^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133297937 10000000000 31586216855909 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241157359/5000000000 : ℝ)^1097 ≤ (35109110493289/100000000000000 : ℝ)^841 := by
    have hnat : (2241157359 : ℕ)^1097*100000000000000^841 ≤ 35109110493289^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241157359 5000000000 35109110493289 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304623169/10000000000 : ℝ), (4133297937/10000000000 : ℝ), (2241157359/5000000000 : ℝ)] ![(6660934528659/20000000000000 : ℝ), (31586216855909/100000000000000 : ℝ), (35109110493289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304623169/10000000000 : ℝ)|^1097 ≤ (6660934528659/20000000000000 : ℝ)^841
        have hw : |(4304623169/10000000000 : ℝ)|=(4304623169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4133297937/10000000000 : ℝ)|^1097 ≤ (31586216855909/100000000000000 : ℝ)^841
        have hw : |(4133297937/10000000000 : ℝ)|=(4133297937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241157359/5000000000 : ℝ)|^1097 ≤ (35109110493289/100000000000000 : ℝ)^841
        have hw : |(2241157359/5000000000 : ℝ)|=(2241157359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s6_4 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-394390779/2000000000 : ℝ)*x 0 + (655932903/1250000000 : ℝ)*x 1 + (1081537597/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (394390779/2000000000 : ℝ)^1097 ≤ (96239565119/800000000000 : ℝ)^841 := by
    have hnat : (394390779 : ℕ)^1097*800000000000^841 ≤ 96239565119^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394390779 2000000000 96239565119 800000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655932903/1250000000 : ℝ)^1097 ≤ (21561160853321/50000000000000 : ℝ)^841 := by
    have hnat : (655932903 : ℕ)^1097*50000000000000^841 ≤ 21561160853321^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655932903 1250000000 21561160853321 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081537597/2000000000 : ℝ)^1097 ≤ (44847732638493/100000000000000 : ℝ)^841 := by
    have hnat : (1081537597 : ℕ)^1097*100000000000000^841 ≤ 44847732638493^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081537597 2000000000 44847732638493 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-394390779/2000000000 : ℝ), (655932903/1250000000 : ℝ), (1081537597/2000000000 : ℝ)] ![(96239565119/800000000000 : ℝ), (21561160853321/50000000000000 : ℝ), (44847732638493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-394390779/2000000000 : ℝ)|^1097 ≤ (96239565119/800000000000 : ℝ)^841
        have hw : |(-394390779/2000000000 : ℝ)|=(394390779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655932903/1250000000 : ℝ)|^1097 ≤ (21561160853321/50000000000000 : ℝ)^841
        have hw : |(655932903/1250000000 : ℝ)|=(655932903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081537597/2000000000 : ℝ)|^1097 ≤ (44847732638493/100000000000000 : ℝ)^841
        have hw : |(1081537597/2000000000 : ℝ)|=(1081537597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s6_5 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652697499/5000000000 : ℝ)*x 0 + (-1893303679/10000000000 : ℝ)*x 1 + (2703844037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652697499/5000000000 : ℝ)^1097 ≤ (43744346160399/100000000000000 : ℝ)^841 := by
    have hnat : (2652697499 : ℕ)^1097*100000000000000^841 ≤ 43744346160399^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652697499 5000000000 43744346160399 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1893303679/10000000000 : ℝ)^1097 ≤ (712995013931/6250000000000 : ℝ)^841 := by
    have hnat : (1893303679 : ℕ)^1097*6250000000000^841 ≤ 712995013931^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893303679 10000000000 712995013931 6250000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703844037/5000000000 : ℝ)^1097 ≤ (22423866800639/50000000000000 : ℝ)^841 := by
    have hnat : (2703844037 : ℕ)^1097*50000000000000^841 ≤ 22423866800639^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703844037 5000000000 22423866800639 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652697499/5000000000 : ℝ), (-1893303679/10000000000 : ℝ), (2703844037/5000000000 : ℝ)] ![(43744346160399/100000000000000 : ℝ), (712995013931/6250000000000 : ℝ), (22423866800639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652697499/5000000000 : ℝ)|^1097 ≤ (43744346160399/100000000000000 : ℝ)^841
        have hw : |(2652697499/5000000000 : ℝ)|=(2652697499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1893303679/10000000000 : ℝ)|^1097 ≤ (712995013931/6250000000000 : ℝ)^841
        have hw : |(-1893303679/10000000000 : ℝ)|=(1893303679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703844037/5000000000 : ℝ)|^1097 ≤ (22423866800639/50000000000000 : ℝ)^841
        have hw : |(2703844037/5000000000 : ℝ)|=(2703844037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s6_6 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305395163/10000000000 : ℝ)*x 0 + (270384403/500000000 : ℝ)*x 1 + (-1893303473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305395163/10000000000 : ℝ)^1097 ≤ (2734021745937/6250000000000 : ℝ)^841 := by
    have hnat : (5305395163 : ℕ)^1097*6250000000000^841 ≤ 2734021745937^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305395163 10000000000 2734021745937 6250000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270384403/500000000 : ℝ)^1097 ≤ (44847733449829/100000000000000 : ℝ)^841 := by
    have hnat : (270384403 : ℕ)^1097*100000000000000^841 ≤ 44847733449829^841*500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270384403 500000000 44847733449829 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1893303473/10000000000 : ℝ)^1097 ≤ (1425989825479/12500000000000 : ℝ)^841 := by
    have hnat : (1893303473 : ℕ)^1097*12500000000000^841 ≤ 1425989825479^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893303473 10000000000 1425989825479 12500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305395163/10000000000 : ℝ), (270384403/500000000 : ℝ), (-1893303473/10000000000 : ℝ)] ![(2734021745937/6250000000000 : ℝ), (44847733449829/100000000000000 : ℝ), (1425989825479/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305395163/10000000000 : ℝ)|^1097 ≤ (2734021745937/6250000000000 : ℝ)^841
        have hw : |(5305395163/10000000000 : ℝ)|=(5305395163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270384403/500000000 : ℝ)|^1097 ≤ (44847733449829/100000000000000 : ℝ)^841
        have hw : |(270384403/500000000 : ℝ)|=(270384403/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1893303473/10000000000 : ℝ)|^1097 ≤ (1425989825479/12500000000000 : ℝ)^841
        have hw : |(-1893303473/10000000000 : ℝ)|=(1893303473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s6_7 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4304647783/10000000000 : ℝ)*x 0 + (2240528021/5000000000 : ℝ)*x 1 + (4134563023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304647783/10000000000 : ℝ)^1097 ≤ (6660984209991/20000000000000 : ℝ)^841 := by
    have hnat : (4304647783 : ℕ)^1097*20000000000000^841 ≤ 6660984209991^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304647783 10000000000 6660984209991 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240528021/5000000000 : ℝ)^1097 ≤ (35096251010541/100000000000000 : ℝ)^841 := by
    have hnat : (2240528021 : ℕ)^1097*100000000000000^841 ≤ 35096251010541^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240528021 5000000000 35096251010541 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4134563023/10000000000 : ℝ)^1097 ≤ (31598827922303/100000000000000 : ℝ)^841 := by
    have hnat : (4134563023 : ℕ)^1097*100000000000000^841 ≤ 31598827922303^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134563023 10000000000 31598827922303 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304647783/10000000000 : ℝ), (2240528021/5000000000 : ℝ), (4134563023/10000000000 : ℝ)] ![(6660984209991/20000000000000 : ℝ), (35096251010541/100000000000000 : ℝ), (31598827922303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304647783/10000000000 : ℝ)|^1097 ≤ (6660984209991/20000000000000 : ℝ)^841
        have hw : |(4304647783/10000000000 : ℝ)|=(4304647783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240528021/5000000000 : ℝ)|^1097 ≤ (35096251010541/100000000000000 : ℝ)^841
        have hw : |(2240528021/5000000000 : ℝ)|=(2240528021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4134563023/10000000000 : ℝ)|^1097 ≤ (31598827922303/100000000000000 : ℝ)^841
        have hw : |(4134563023/10000000000 : ℝ)|=(4134563023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1428_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5669/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14757/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5667/50000 : ℝ) ^ (4387/1024 : ℝ) ≤ (8888075782191147/100000000000000000000 : ℝ) := by
    have hpowers : (5667/50000 : ℝ)^4387 ≤ (8888075782191147/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5667 : ℕ)^4387*100000000000000000000^1024 ≤ 8888075782191147^1024*50000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5667 50000 8888075782191147 100000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5667/50000 : ℝ)) (X := (8888075782191147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (369/2500 : ℝ) ^ (4387/1024 : ℝ) ≤ (13778015056674723/50000000000000000000 : ℝ) := by
    have hpowers : (369/2500 : ℝ)^4387 ≤ (13778015056674723/50000000000000000000 : ℝ)^1024 := by
      have hnat : (369 : ℕ)^4387*50000000000000000000^1024 ≤ 13778015056674723^1024*2500^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        369 2500 13778015056674723 50000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (369/2500 : ℝ)) (X := (13778015056674723/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008888075782191147/50000000000000000000 : ℝ) ≤ (10000414897175627/10000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (50008888075782191147/50000000000000000000 : ℝ)^1024 ≤ (10000414897175627/10000000000000000 : ℝ)^4387 := by
      have hnat : (50008888075782191147 : ℕ)^1024*10000000000000000^4387 ≤ 10000414897175627^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008888075782191147 50000000000000000000 10000414897175627 10000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000414897175627/10000000000000000 : ℝ)) (X := (50008888075782191147/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036444105895540593/100000000000000000000 : ℝ) ≤ (200017010965399/200000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (100036444105895540593/100000000000000000000 : ℝ)^1024 ≤ (200017010965399/200000000000000 : ℝ)^4387 := by
      have hnat : (100036444105895540593 : ℕ)^1024*200000000000000^4387 ≤ 200017010965399^4387*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036444105895540593 100000000000000000000 200017010965399 200000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200017010965399/200000000000000 : ℝ)) (X := (100036444105895540593/100000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013778015056674723/25000000000000000000 : ℝ) ≤ (10001286199364273/10000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (25013778015056674723/25000000000000000000 : ℝ)^1024 ≤ (10001286199364273/10000000000000000 : ℝ)^4387 := by
      have hnat : (25013778015056674723 : ℕ)^1024*10000000000000000^4387 ≤ 10001286199364273^4387*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013778015056674723 25000000000000000000 10001286199364273 10000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001286199364273/10000000000000000 : ℝ)) (X := (25013778015056674723/25000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8888075782191147/100000000000000000000 : ℝ) ≤ ((5708591016452930723/5710000000000000000 : ℝ)+2*(145217031441/114200000000000 : ℝ)*(5667/50000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (5708591016452930723/5710000000000000000 : ℝ)+2*(145217031441/114200000000000 : ℝ)*(5667/50000 : ℝ)=(10000414897175627/10000000000000000 : ℝ) by norm_num, show 1+2*(8888075782191147/100000000000000000000 : ℝ)=(50008888075782191147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13778015056674723/50000000000000000000 : ℝ)+(8888075782191147/100000000000000000000 : ℝ) ≤ ((5708591016452930723/5710000000000000000 : ℝ)+(145217031441/114200000000000 : ℝ)*((369/2500 : ℝ)+(5667/50000 : ℝ)))^(4387/1024 : ℝ) := by
    rw [show (5708591016452930723/5710000000000000000 : ℝ)+(145217031441/114200000000000 : ℝ)*((369/2500 : ℝ)+(5667/50000 : ℝ))=(200017010965399/200000000000000 : ℝ) by norm_num, show 1+(13778015056674723/50000000000000000000 : ℝ)+(8888075782191147/100000000000000000000 : ℝ)=(100036444105895540593/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13778015056674723/50000000000000000000 : ℝ) ≤ ((5708591016452930723/5710000000000000000 : ℝ)+2*(145217031441/114200000000000 : ℝ)*(369/2500 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (5708591016452930723/5710000000000000000 : ℝ)+2*(145217031441/114200000000000 : ℝ)*(369/2500 : ℝ)=(10001286199364273/10000000000000000 : ℝ) by norm_num, show 1+2*(13778015056674723/50000000000000000000 : ℝ)=(25013778015056674723/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5708591016452930723/5710000000000000000 : ℝ)*(X 1 0+X 2 0)+(145217031441/114200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (5708591016452930723/5710000000000000000 : ℝ)) (alpha := (145217031441/114200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5708591016452930723/5710000000000000000 : ℝ)*(X 0 1+X 2 1)+(145217031441/114200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (5708591016452930723/5710000000000000000 : ℝ)) (alpha := (145217031441/114200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5708591016452930723/5710000000000000000 : ℝ)*(X 0 2+X 1 2)+(145217031441/114200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (5708591016452930723/5710000000000000000 : ℝ)) (alpha := (145217031441/114200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1971942487/10000000000 : ℝ)*X 0 0+(2704136559/5000000000 : ℝ)*X 0 1+(2623440579/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347348609/10000000000 : ℝ)*X 1 0+(-2054110439/10000000000 : ℝ)*X 1 1+(5246881131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069469721/2000000000 : ℝ)*X 2 0+(5246881193/10000000000 : ℝ)*X 2 1+(-2054110361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4304623169/10000000000 : ℝ)*X 0 0+(4133297937/10000000000 : ℝ)*X 0 1+(2241157359/5000000000 : ℝ)*X 0 2+(4304623169/10000000000 : ℝ)*X 1 0+(4133297937/10000000000 : ℝ)*X 1 1+(2241157359/5000000000 : ℝ)*X 1 2+(4304623169/10000000000 : ℝ)*X 2 0+(4133297937/10000000000 : ℝ)*X 2 1+(2241157359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-394390779/2000000000 : ℝ)*X 0 0+(655932903/1250000000 : ℝ)*X 0 1+(1081537597/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652697499/5000000000 : ℝ)*X 1 0+(-1893303679/10000000000 : ℝ)*X 1 1+(2703844037/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305395163/10000000000 : ℝ)*X 2 0+(270384403/500000000 : ℝ)*X 2 1+(-1893303473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4304647783/10000000000 : ℝ)*X 0 0+(2240528021/5000000000 : ℝ)*X 0 1+(4134563023/10000000000 : ℝ)*X 0 2+(4304647783/10000000000 : ℝ)*X 1 0+(2240528021/5000000000 : ℝ)*X 1 1+(4134563023/10000000000 : ℝ)*X 1 2+(4304647783/10000000000 : ℝ)*X 2 0+(2240528021/5000000000 : ℝ)*X 2 1+(4134563023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16461826023554251340247/2855000000000000000000000000 : ℝ) := by norm_num
    linear_combination (506553319/50000000000000 : ℝ)*(base19) + (944502951/100000000000000 : ℝ)*(base23) + (34206327/100000000000000 : ℝ)*(lower2) + (84466437/100000000000000 : ℝ)*(upper3) + (135994813/100000000000000 : ℝ)*(upper5) + (2265337894743079/50000000000000 : ℝ)*(major0) + (2265337894743079/50000000000000 : ℝ)*(major1) + (2265337894743079/50000000000000 : ℝ)*(major2) + (6196116166408163/100000000000000 : ℝ)*(sp0) + (6196138805631517/100000000000000 : ℝ)*(sp1) + (1549034718558801/25000000000000 : ℝ)*(sp2) + (1432600934729293/50000000000000 : ℝ)*(sp3) + (23652329991/100000000000000 : ℝ)*(sp4) + (484928839/5000000000000 : ℝ)*(sp7) + (1432605784017683/50000000000000 : ℝ)*(f.failure) + (3098069909369077/50000000000000 : ℝ)*(f.sum) + (6277552337201/2855000000000000000000000000 : ℝ)*base66 + (885879067617333883/285500000000000000000000000000000 : ℝ)*base68 + (338981449779166117/285500000000000000000000000000000 : ℝ)*base69 + (1729963405495833883/285500000000000000000000000000000 : ℝ)*base72 + (142117393853/1427500000000000000000000000 : ℝ)*base74 + (191019693530166117/285500000000000000000000000000000 : ℝ)*base75 + (3087453257374333883/285500000000000000000000000000000 : ℝ)*base78 + (1434463610915666117/285500000000000000000000000000000 : ℝ)*base79 + (22661999291219/2855000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (21298399/2500000000000000000000 : ℝ)*base90 + (21298399/2500000000000000000000 : ℝ)*base92 + (21298399/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32761407808887933226887/2855000000000000000000000000 : ℝ) := by norm_num
    linear_combination (439739823/25000000000000 : ℝ)*(base19) + (2163953079/100000000000000 : ℝ)*(base23) + (282462931/50000000000000 : ℝ)*(lower1) + (1193559/400000000000 : ℝ)*(upper3) + (5546797/10000000000000 : ℝ)*(lower4) + (232355527/100000000000000 : ℝ)*(upper5) + (2281810585641011/50000000000000 : ℝ)*(major0) + (2281810585641011/50000000000000 : ℝ)*(major1) + (2281810585641011/50000000000000 : ℝ)*(major2) + (3361914297/25000000000000 : ℝ)*(sp2) + (3120597821936393/50000000000000 : ℝ)*(sp4) + (3120596942456747/50000000000000 : ℝ)*(sp5) + (6241180032262519/100000000000000 : ℝ)*(sp6) + (360755789523491/12500000000000 : ℝ)*(sp7) + (360755789523491/12500000000000 : ℝ)*(f.failure) + (3120597821936393/50000000000000 : ℝ)*(f.sum) + (4365147077181/2855000000000000000000000000 : ℝ)*base65 + (30911350605953230953/285500000000000000000000000000000 : ℝ)*base67 + (1879232145293769047/285500000000000000000000000000000 : ℝ)*base70 + (33664603089295230953/285500000000000000000000000000000 : ℝ)*base71 + (9088589276601/2855000000000000000000000000 : ℝ)*base73 + (9389250931076769047/285500000000000000000000000000000 : ℝ)*base76 + (106768035992269047/285500000000000000000000000000000 : ℝ)*base78 + (1521733260173230953/285500000000000000000000000000000 : ℝ)*base79 + (1264095019593/356875000000000000000000000 : ℝ)*base82 + (782577/625000000000000000000 : ℝ)*base89 + (782577/625000000000000000000 : ℝ)*base91 + (782577/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1428_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1428_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1428_s7_0 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347343073/10000000000 : ℝ)*x 0 + (5246905491/10000000000 : ℝ)*x 1 + (-2054085439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347343073/10000000000 : ℝ)^1097 ≤ (2762252764307/6250000000000 : ℝ)^841 := by
    have hnat : (5347343073 : ℕ)^1097*6250000000000^841 ≤ 2762252764307^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347343073 10000000000 2762252764307 6250000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246905491/10000000000 : ℝ)^1097 ≤ (10779085834541/25000000000000 : ℝ)^841 := by
    have hnat : (5246905491 : ℕ)^1097*25000000000000^841 ≤ 10779085834541^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246905491 10000000000 10779085834541 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054085439/10000000000 : ℝ)^1097 ≤ (12687612423701/100000000000000 : ℝ)^841 := by
    have hnat : (2054085439 : ℕ)^1097*100000000000000^841 ≤ 12687612423701^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054085439 10000000000 12687612423701 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347343073/10000000000 : ℝ), (5246905491/10000000000 : ℝ), (-2054085439/10000000000 : ℝ)] ![(2762252764307/6250000000000 : ℝ), (10779085834541/25000000000000 : ℝ), (12687612423701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347343073/10000000000 : ℝ)|^1097 ≤ (2762252764307/6250000000000 : ℝ)^841
        have hw : |(5347343073/10000000000 : ℝ)|=(5347343073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246905491/10000000000 : ℝ)|^1097 ≤ (10779085834541/25000000000000 : ℝ)^841
        have hw : |(5246905491/10000000000 : ℝ)|=(5246905491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054085439/10000000000 : ℝ)|^1097 ≤ (12687612423701/100000000000000 : ℝ)^841
        have hw : |(-2054085439/10000000000 : ℝ)|=(2054085439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s7_1 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-985976943/5000000000 : ℝ)*x 0 + (2623743537/5000000000 : ℝ)*x 1 + (5407664359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (985976943/5000000000 : ℝ)^1097 ≤ (12029945568257/100000000000000 : ℝ)^841 := by
    have hnat : (985976943 : ℕ)^1097*100000000000000^841 ≤ 12029945568257^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985976943 5000000000 12029945568257 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623743537/5000000000 : ℝ)^1097 ≤ (21561288680161/50000000000000 : ℝ)^841 := by
    have hnat : (2623743537 : ℕ)^1097*50000000000000^841 ≤ 21561288680161^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623743537 5000000000 21561288680161 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407664359/10000000000 : ℝ)^1097 ≤ (11211869264249/25000000000000 : ℝ)^841 := by
    have hnat : (5407664359 : ℕ)^1097*25000000000000^841 ≤ 11211869264249^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407664359 10000000000 11211869264249 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-985976943/5000000000 : ℝ), (2623743537/5000000000 : ℝ), (5407664359/10000000000 : ℝ)] ![(12029945568257/100000000000000 : ℝ), (21561288680161/50000000000000 : ℝ), (11211869264249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-985976943/5000000000 : ℝ)|^1097 ≤ (12029945568257/100000000000000 : ℝ)^841
        have hw : |(-985976943/5000000000 : ℝ)|=(985976943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623743537/5000000000 : ℝ)|^1097 ≤ (21561288680161/50000000000000 : ℝ)^841
        have hw : |(2623743537/5000000000 : ℝ)|=(2623743537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407664359/10000000000 : ℝ)|^1097 ≤ (11211869264249/25000000000000 : ℝ)^841
        have hw : |(5407664359/10000000000 : ℝ)|=(5407664359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s7_2 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326350549/2500000000 : ℝ)*x 0 + (-1893326481/10000000000 : ℝ)*x 1 + (168989511/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326350549/2500000000 : ℝ)^1097 ≤ (43744423575693/100000000000000 : ℝ)^841 := by
    have hnat : (1326350549 : ℕ)^1097*100000000000000^841 ≤ 43744423575693^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326350549 2500000000 43744423575693 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1893326481/10000000000 : ℝ)^1097 ≤ (11408099436331/100000000000000 : ℝ)^841 := by
    have hnat : (1893326481 : ℕ)^1097*100000000000000^841 ≤ 11408099436331^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893326481 10000000000 11408099436331 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168989511/312500000 : ℝ)^1097 ≤ (5605934622659/12500000000000 : ℝ)^841 := by
    have hnat : (168989511 : ℕ)^1097*12500000000000^841 ≤ 5605934622659^841*312500000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168989511 312500000 5605934622659 12500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326350549/2500000000 : ℝ), (-1893326481/10000000000 : ℝ), (168989511/312500000 : ℝ)] ![(43744423575693/100000000000000 : ℝ), (11408099436331/100000000000000 : ℝ), (5605934622659/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326350549/2500000000 : ℝ)|^1097 ≤ (43744423575693/100000000000000 : ℝ)^841
        have hw : |(1326350549/2500000000 : ℝ)|=(1326350549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1893326481/10000000000 : ℝ)|^1097 ≤ (11408099436331/100000000000000 : ℝ)^841
        have hw : |(-1893326481/10000000000 : ℝ)|=(1893326481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168989511/312500000 : ℝ)|^1097 ≤ (5605934622659/12500000000000 : ℝ)^841
        have hw : |(168989511/312500000 : ℝ)|=(168989511/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s7_3 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (663175273/1250000000 : ℝ)*x 0 + (5407664357/10000000000 : ℝ)*x 1 + (-1893326489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663175273/1250000000 : ℝ)^1097 ≤ (5468052930829/12500000000000 : ℝ)^841 := by
    have hnat : (663175273 : ℕ)^1097*12500000000000^841 ≤ 5468052930829^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663175273 1250000000 5468052930829 12500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407664357/10000000000 : ℝ)^1097 ≤ (44847477035361/100000000000000 : ℝ)^841 := by
    have hnat : (5407664357 : ℕ)^1097*100000000000000^841 ≤ 44847477035361^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407664357 10000000000 44847477035361 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1893326489/10000000000 : ℝ)^1097 ≤ (1426012437401/12500000000000 : ℝ)^841 := by
    have hnat : (1893326489 : ℕ)^1097*12500000000000^841 ≤ 1426012437401^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893326489 10000000000 1426012437401 12500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663175273/1250000000 : ℝ), (5407664357/10000000000 : ℝ), (-1893326489/10000000000 : ℝ)] ![(5468052930829/12500000000000 : ℝ), (44847477035361/100000000000000 : ℝ), (1426012437401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663175273/1250000000 : ℝ)|^1097 ≤ (5468052930829/12500000000000 : ℝ)^841
        have hw : |(663175273/1250000000 : ℝ)|=(663175273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407664357/10000000000 : ℝ)|^1097 ≤ (44847477035361/100000000000000 : ℝ)^841
        have hw : |(5407664357/10000000000 : ℝ)|=(5407664357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1893326489/10000000000 : ℝ)|^1097 ≤ (1426012437401/12500000000000 : ℝ)^841
        have hw : |(-1893326489/10000000000 : ℝ)|=(1893326489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s7_4 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4304649391/10000000000 : ℝ)*x 0 + (4481004401/10000000000 : ℝ)*x 1 + (4134614317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304649391/10000000000 : ℝ)^1097 ≤ (1040779289939/3125000000000 : ℝ)^841 := by
    have hnat : (4304649391 : ℕ)^1097*3125000000000^841 ≤ 1040779289939^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304649391 10000000000 1040779289939 3125000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481004401/10000000000 : ℝ)^1097 ≤ (35095723434741/100000000000000 : ℝ)^841 := by
    have hnat : (4481004401 : ℕ)^1097*100000000000000^841 ≤ 35095723434741^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481004401 10000000000 35095723434741 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4134614317/10000000000 : ℝ)^1097 ≤ (15799669636809/50000000000000 : ℝ)^841 := by
    have hnat : (4134614317 : ℕ)^1097*50000000000000^841 ≤ 15799669636809^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134614317 10000000000 15799669636809 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304649391/10000000000 : ℝ), (4481004401/10000000000 : ℝ), (4134614317/10000000000 : ℝ)] ![(1040779289939/3125000000000 : ℝ), (35095723434741/100000000000000 : ℝ), (15799669636809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304649391/10000000000 : ℝ)|^1097 ≤ (1040779289939/3125000000000 : ℝ)^841
        have hw : |(4304649391/10000000000 : ℝ)|=(4304649391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481004401/10000000000 : ℝ)|^1097 ≤ (35095723434741/100000000000000 : ℝ)^841
        have hw : |(4481004401/10000000000 : ℝ)|=(4481004401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4134614317/10000000000 : ℝ)|^1097 ≤ (15799669636809/50000000000000 : ℝ)^841
        have hw : |(4134614317/10000000000 : ℝ)|=(4134614317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1428_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5669/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3689/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5669/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5669/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5669/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5669/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5669/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5669/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5669/50000 : ℝ) ^ (4387/1024 : ℝ) ≤ (8901522116037499/100000000000000000000 : ℝ) := by
    have hpowers : (5669/50000 : ℝ)^4387 ≤ (8901522116037499/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5669 : ℕ)^4387*100000000000000000000^1024 ≤ 8901522116037499^1024*50000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5669 50000 8901522116037499 100000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5669/50000 : ℝ)) (X := (8901522116037499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14757/100000 : ℝ) ^ (4387/1024 : ℝ) ≤ (27532043205062891/100000000000000000000 : ℝ) := by
    have hpowers : (14757/100000 : ℝ)^4387 ≤ (27532043205062891/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14757 : ℕ)^4387*100000000000000000000^1024 ≤ 27532043205062891^1024*100000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14757 100000 27532043205062891 100000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14757/100000 : ℝ)) (X := (27532043205062891/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008901522116037499/50000000000000000000 : ℝ) ≤ (5000207762405193/5000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (50008901522116037499/50000000000000000000 : ℝ)^1024 ≤ (5000207762405193/5000000000000000 : ℝ)^4387 := by
      have hnat : (50008901522116037499 : ℕ)^1024*5000000000000000^4387 ≤ 5000207762405193^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008901522116037499 50000000000000000000 5000207762405193 5000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000207762405193/5000000000000000 : ℝ)) (X := (50008901522116037499/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003643356532110039/10000000000000000000 : ℝ) ≤ (5000425151151909/5000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (10003643356532110039/10000000000000000000 : ℝ)^1024 ≤ (5000425151151909/5000000000000000 : ℝ)^4387 := by
      have hnat : (10003643356532110039 : ℕ)^1024*5000000000000000^4387 ≤ 5000425151151909^4387*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003643356532110039 10000000000000000000 5000425151151909 5000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000425151151909/5000000000000000 : ℝ)) (X := (10003643356532110039/10000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027532043205062891/50000000000000000000 : ℝ) ≤ (40005140319189/40000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (50027532043205062891/50000000000000000000 : ℝ)^1024 ≤ (40005140319189/40000000000000 : ℝ)^4387 := by
      have hnat : (50027532043205062891 : ℕ)^1024*40000000000000^4387 ≤ 40005140319189^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027532043205062891 50000000000000000000 40005140319189 40000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40005140319189/40000000000000 : ℝ)) (X := (50027532043205062891/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8901522116037499/100000000000000000000 : ℝ) ≤ ((17090780832442822851/17095000000000000000 : ℝ)+2*(54347186679/42737500000000 : ℝ)*(5669/50000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (17090780832442822851/17095000000000000000 : ℝ)+2*(54347186679/42737500000000 : ℝ)*(5669/50000 : ℝ)=(5000207762405193/5000000000000000 : ℝ) by norm_num, show 1+2*(8901522116037499/100000000000000000000 : ℝ)=(50008901522116037499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27532043205062891/100000000000000000000 : ℝ)+(8901522116037499/100000000000000000000 : ℝ) ≤ ((17090780832442822851/17095000000000000000 : ℝ)+(54347186679/42737500000000 : ℝ)*((14757/100000 : ℝ)+(5669/50000 : ℝ)))^(4387/1024 : ℝ) := by
    rw [show (17090780832442822851/17095000000000000000 : ℝ)+(54347186679/42737500000000 : ℝ)*((14757/100000 : ℝ)+(5669/50000 : ℝ))=(5000425151151909/5000000000000000 : ℝ) by norm_num, show 1+(27532043205062891/100000000000000000000 : ℝ)+(8901522116037499/100000000000000000000 : ℝ)=(10003643356532110039/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27532043205062891/100000000000000000000 : ℝ) ≤ ((17090780832442822851/17095000000000000000 : ℝ)+2*(54347186679/42737500000000 : ℝ)*(14757/100000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (17090780832442822851/17095000000000000000 : ℝ)+2*(54347186679/42737500000000 : ℝ)*(14757/100000 : ℝ)=(40005140319189/40000000000000 : ℝ) by norm_num, show 1+2*(27532043205062891/100000000000000000000 : ℝ)=(50027532043205062891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17090780832442822851/17095000000000000000 : ℝ)*(X 1 0+X 2 0)+(54347186679/42737500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (17090780832442822851/17095000000000000000 : ℝ)) (alpha := (54347186679/42737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17090780832442822851/17095000000000000000 : ℝ)*(X 0 1+X 2 1)+(54347186679/42737500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (17090780832442822851/17095000000000000000 : ℝ)) (alpha := (54347186679/42737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17090780832442822851/17095000000000000000 : ℝ)*(X 0 2+X 1 2)+(54347186679/42737500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (17090780832442822851/17095000000000000000 : ℝ)) (alpha := (54347186679/42737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5347343073/10000000000 : ℝ)*X 2 0+(5246905491/10000000000 : ℝ)*X 2 1+(-2054085439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-985976943/5000000000 : ℝ)*X 0 0+(2623743537/5000000000 : ℝ)*X 0 1+(5407664359/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1326350549/2500000000 : ℝ)*X 1 0+(-1893326481/10000000000 : ℝ)*X 1 1+(168989511/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((663175273/1250000000 : ℝ)*X 2 0+(5407664357/10000000000 : ℝ)*X 2 1+(-1893326489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4304649391/10000000000 : ℝ)*X 0 0+(4481004401/10000000000 : ℝ)*X 0 1+(4134614317/10000000000 : ℝ)*X 0 2+(4304649391/10000000000 : ℝ)*X 1 0+(4481004401/10000000000 : ℝ)*X 1 1+(4134614317/10000000000 : ℝ)*X 1 2+(4304649391/10000000000 : ℝ)*X 2 0+(4481004401/10000000000 : ℝ)*X 2 1+(4134614317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1088753989350154657122818427/170950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (266441881/25000000000000 : ℝ)*(base19) + (579712761/50000000000000 : ℝ)*(base23) + (11218313/3125000000000 : ℝ)*(lower1) + (25216013/20000000000000 : ℝ)*(upper3) + (50560263/100000000000000 : ℝ)*(lower4) + (128876281/100000000000000 : ℝ)*(upper5) + (912996700785341/20000000000000 : ℝ)*(major0) + (912996700785341/20000000000000 : ℝ)*(major1) + (912996700785341/20000000000000 : ℝ)*(major2) + (49330851/3125000000000 : ℝ)*(sp0) + (3121529468269047/50000000000000 : ℝ)*(sp1) + (624305787077057/10000000000000 : ℝ)*(sp2) + (312152809926267/5000000000000 : ℝ)*(sp3) + (1443453929510241/50000000000000 : ℝ)*(sp4) + (1443453929510241/50000000000000 : ℝ)*(f.failure) + (3121529468269047/50000000000000 : ℝ)*(f.sum) + (86729020473/341900000000000000000000000 : ℝ)*base65 + (104188654916613293/26300000000000000000000000000000 : ℝ)*base68 + (303027544940786707/26300000000000000000000000000000 : ℝ)*base69 + (1495052581443813293/26300000000000000000000000000000 : ℝ)*base72 + (263586979101/213687500000000000000000000 : ℝ)*base74 + (1081767155028586707/26300000000000000000000000000000 : ℝ)*base75 + (75409449947386707/26300000000000000000000000000000 : ℝ)*base77 + (208544636246586707/26300000000000000000000000000000 : ℝ)*base79 + (6889227374439/1709500000000000000000000000 : ℝ)*base81 + (1284827/2500000000000000000000 : ℝ)*base89 + (1284827/2500000000000000000000 : ℝ)*base91 + (1284827/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1428_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1428_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1428_box_0 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1811209499/10000000000 : ℝ)*x 0 + (1346574887/2500000000 : ℝ)*x 1 + (673287539/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1811209499/10000000000 : ℝ)^1097 ≤ (2691749971841/25000000000000 : ℝ)^841 := by
    have hnat : (1811209499 : ℕ)^1097*25000000000000^841 ≤ 2691749971841^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811209499 10000000000 2691749971841 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346574887/2500000000 : ℝ)^1097 ≤ (11154123980853/25000000000000 : ℝ)^841 := by
    have hnat : (1346574887 : ℕ)^1097*25000000000000^841 ≤ 11154123980853^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346574887 2500000000 11154123980853 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673287539/1250000000 : ℝ)^1097 ≤ (22308252089129/50000000000000 : ℝ)^841 := by
    have hnat : (673287539 : ℕ)^1097*50000000000000^841 ≤ 22308252089129^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673287539 1250000000 22308252089129 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1811209499/10000000000 : ℝ), (1346574887/2500000000 : ℝ), (673287539/1250000000 : ℝ)] ![(2691749971841/25000000000000 : ℝ), (11154123980853/25000000000000 : ℝ), (22308252089129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1811209499/10000000000 : ℝ)|^1097 ≤ (2691749971841/25000000000000 : ℝ)^841
        have hw : |(-1811209499/10000000000 : ℝ)|=(1811209499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346574887/2500000000 : ℝ)|^1097 ≤ (11154123980853/25000000000000 : ℝ)^841
        have hw : |(1346574887/2500000000 : ℝ)|=(1346574887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673287539/1250000000 : ℝ)|^1097 ≤ (22308252089129/50000000000000 : ℝ)^841
        have hw : |(673287539/1250000000 : ℝ)|=(673287539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_1 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2643028129/5000000000 : ℝ)*x 0 + (-974463159/5000000000 : ℝ)*x 1 + (5386299807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643028129/5000000000 : ℝ)^1097 ≤ (21768235690463/50000000000000 : ℝ)^841 := by
    have hnat : (2643028129 : ℕ)^1097*50000000000000^841 ≤ 21768235690463^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643028129 5000000000 21768235690463 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974463159/5000000000 : ℝ)^1097 ≤ (1184702988561/10000000000000 : ℝ)^841 := by
    have hnat : (974463159 : ℕ)^1097*10000000000000^841 ≤ 1184702988561^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974463159 5000000000 1184702988561 10000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386299807/10000000000 : ℝ)^1097 ≤ (5577062340231/12500000000000 : ℝ)^841 := by
    have hnat : (5386299807 : ℕ)^1097*12500000000000^841 ≤ 5577062340231^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386299807 10000000000 5577062340231 12500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643028129/5000000000 : ℝ), (-974463159/5000000000 : ℝ), (5386299807/10000000000 : ℝ)] ![(21768235690463/50000000000000 : ℝ), (1184702988561/10000000000000 : ℝ), (5577062340231/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643028129/5000000000 : ℝ)|^1097 ≤ (21768235690463/50000000000000 : ℝ)^841
        have hw : |(2643028129/5000000000 : ℝ)|=(2643028129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-974463159/5000000000 : ℝ)|^1097 ≤ (1184702988561/10000000000000 : ℝ)^841
        have hw : |(-974463159/5000000000 : ℝ)|=(974463159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386299807/10000000000 : ℝ)|^1097 ≤ (5577062340231/12500000000000 : ℝ)^841
        have hw : |(5386299807/10000000000 : ℝ)|=(5386299807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_2 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2643028281/5000000000 : ℝ)*x 0 + (673287463/1250000000 : ℝ)*x 1 + (-974463023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643028281/5000000000 : ℝ)^1097 ≤ (43536474646847/100000000000000 : ℝ)^841 := by
    have hnat : (2643028281 : ℕ)^1097*100000000000000^841 ≤ 43536474646847^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643028281 5000000000 43536474646847 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673287463/1250000000 : ℝ)^1097 ≤ (11154124402239/25000000000000 : ℝ)^841 := by
    have hnat : (673287463 : ℕ)^1097*25000000000000^841 ≤ 11154124402239^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673287463 1250000000 11154124402239 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974463023/5000000000 : ℝ)^1097 ≤ (11847027728891/100000000000000 : ℝ)^841 := by
    have hnat : (974463023 : ℕ)^1097*100000000000000^841 ≤ 11847027728891^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974463023 5000000000 11847027728891 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643028281/5000000000 : ℝ), (673287463/1250000000 : ℝ), (-974463023/5000000000 : ℝ)] ![(43536474646847/100000000000000 : ℝ), (11154124402239/25000000000000 : ℝ), (11847027728891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643028281/5000000000 : ℝ)|^1097 ≤ (43536474646847/100000000000000 : ℝ)^841
        have hw : |(2643028281/5000000000 : ℝ)|=(2643028281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673287463/1250000000 : ℝ)|^1097 ≤ (11154124402239/25000000000000 : ℝ)^841
        have hw : |(673287463/1250000000 : ℝ)|=(673287463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-974463023/5000000000 : ℝ)|^1097 ≤ (11847027728891/100000000000000 : ℝ)^841
        have hw : |(-974463023/5000000000 : ℝ)|=(974463023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_3 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (445094437/1000000000 : ℝ)*x 0 + (1058793959/2500000000 : ℝ)*x 1 + (2117587803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445094437/1000000000 : ℝ)^1097 ≤ (34788938132929/100000000000000 : ℝ)^841 := by
    have hnat : (445094437 : ℕ)^1097*100000000000000^841 ≤ 34788938132929^841*1000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445094437 1000000000 34788938132929 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058793959/2500000000 : ℝ)^1097 ≤ (32605532080509/100000000000000 : ℝ)^841 := by
    have hnat : (1058793959 : ℕ)^1097*100000000000000^841 ≤ 32605532080509^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058793959 2500000000 32605532080509 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117587803/5000000000 : ℝ)^1097 ≤ (6521105954159/20000000000000 : ℝ)^841 := by
    have hnat : (2117587803 : ℕ)^1097*20000000000000^841 ≤ 6521105954159^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117587803 5000000000 6521105954159 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445094437/1000000000 : ℝ), (1058793959/2500000000 : ℝ), (2117587803/5000000000 : ℝ)] ![(34788938132929/100000000000000 : ℝ), (32605532080509/100000000000000 : ℝ), (6521105954159/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445094437/1000000000 : ℝ)|^1097 ≤ (34788938132929/100000000000000 : ℝ)^841
        have hw : |(445094437/1000000000 : ℝ)|=(445094437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058793959/2500000000 : ℝ)|^1097 ≤ (32605532080509/100000000000000 : ℝ)^841
        have hw : |(1058793959/2500000000 : ℝ)|=(1058793959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117587803/5000000000 : ℝ)|^1097 ≤ (6521105954159/20000000000000 : ℝ)^841
        have hw : |(2117587803/5000000000 : ℝ)|=(2117587803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_4 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135415227/10000000000 : ℝ)*x 0 + (32915687/62500000 : ℝ)*x 1 + (5266510097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135415227/10000000000 : ℝ)^1097 ≤ (6673398836861/50000000000000 : ℝ)^841 := by
    have hnat : (2135415227 : ℕ)^1097*50000000000000^841 ≤ 6673398836861^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135415227 10000000000 6673398836861 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32915687/62500000 : ℝ)^1097 ≤ (43326600209839/100000000000000 : ℝ)^841 := by
    have hnat : (32915687 : ℕ)^1097*100000000000000^841 ≤ 43326600209839^841*62500000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32915687 62500000 43326600209839 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266510097/10000000000 : ℝ)^1097 ≤ (10831650527309/25000000000000 : ℝ)^841 := by
    have hnat : (5266510097 : ℕ)^1097*25000000000000^841 ≤ 10831650527309^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266510097 10000000000 10831650527309 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135415227/10000000000 : ℝ), (32915687/62500000 : ℝ), (5266510097/10000000000 : ℝ)] ![(6673398836861/50000000000000 : ℝ), (43326600209839/100000000000000 : ℝ), (10831650527309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135415227/10000000000 : ℝ)|^1097 ≤ (6673398836861/50000000000000 : ℝ)^841
        have hw : |(-2135415227/10000000000 : ℝ)|=(2135415227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32915687/62500000 : ℝ)|^1097 ≤ (43326600209839/100000000000000 : ℝ)^841
        have hw : |(32915687/62500000 : ℝ)|=(32915687/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266510097/10000000000 : ℝ)|^1097 ≤ (10831650527309/25000000000000 : ℝ)^841
        have hw : |(5266510097/10000000000 : ℝ)|=(5266510097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_5 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369895099/10000000000 : ℝ)*x 0 + (-1997555513/10000000000 : ℝ)*x 1 + (1316627379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369895099/10000000000 : ℝ)^1097 ≤ (44439331818187/100000000000000 : ℝ)^841 := by
    have hnat : (5369895099 : ℕ)^1097*100000000000000^841 ≤ 44439331818187^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369895099 10000000000 44439331818187 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1997555513/10000000000 : ℝ)^1097 ≤ (6117036143833/50000000000000 : ℝ)^841 := by
    have hnat : (1997555513 : ℕ)^1097*50000000000000^841 ≤ 6117036143833^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997555513 10000000000 6117036143833 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316627379/2500000000 : ℝ)^1097 ≤ (21663297937247/50000000000000 : ℝ)^841 := by
    have hnat : (1316627379 : ℕ)^1097*50000000000000^841 ≤ 21663297937247^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316627379 2500000000 21663297937247 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369895099/10000000000 : ℝ), (-1997555513/10000000000 : ℝ), (1316627379/2500000000 : ℝ)] ![(44439331818187/100000000000000 : ℝ), (6117036143833/50000000000000 : ℝ), (21663297937247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369895099/10000000000 : ℝ)|^1097 ≤ (44439331818187/100000000000000 : ℝ)^841
        have hw : |(5369895099/10000000000 : ℝ)|=(5369895099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1997555513/10000000000 : ℝ)|^1097 ≤ (6117036143833/50000000000000 : ℝ)^841
        have hw : |(-1997555513/10000000000 : ℝ)|=(1997555513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316627379/2500000000 : ℝ)|^1097 ≤ (21663297937247/50000000000000 : ℝ)^841
        have hw : |(1316627379/2500000000 : ℝ)|=(1316627379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_6 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1342473611/2500000000 : ℝ)*x 0 + (2633255359/5000000000 : ℝ)*x 1 + (-62423587/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342473611/2500000000 : ℝ)^1097 ≤ (4443932474763/10000000000000 : ℝ)^841 := by
    have hnat : (1342473611 : ℕ)^1097*10000000000000^841 ≤ 4443932474763^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342473611 2500000000 4443932474763 10000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633255359/5000000000 : ℝ)^1097 ≤ (2166330438661/5000000000000 : ℝ)^841 := by
    have hnat : (2633255359 : ℕ)^1097*5000000000000^841 ≤ 2166330438661^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633255359 5000000000 2166330438661 5000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62423587/312500000 : ℝ)^1097 ≤ (2446813292763/20000000000000 : ℝ)^841 := by
    have hnat : (62423587 : ℕ)^1097*20000000000000^841 ≤ 2446813292763^841*312500000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62423587 312500000 2446813292763 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342473611/2500000000 : ℝ), (2633255359/5000000000 : ℝ), (-62423587/312500000 : ℝ)] ![(4443932474763/10000000000000 : ℝ), (2166330438661/5000000000000 : ℝ), (2446813292763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342473611/2500000000 : ℝ)|^1097 ≤ (4443932474763/10000000000000 : ℝ)^841
        have hw : |(1342473611/2500000000 : ℝ)|=(1342473611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633255359/5000000000 : ℝ)|^1097 ≤ (2166330438661/5000000000000 : ℝ)^841
        have hw : |(2633255359/5000000000 : ℝ)|=(2633255359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62423587/312500000 : ℝ)|^1097 ≤ (2446813292763/20000000000000 : ℝ)^841
        have hw : |(-62423587/312500000 : ℝ)|=(62423587/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_7 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (207862897/500000000 : ℝ)*x 0 + (438196771/1000000000 : ℝ)*x 1 + (4381968311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207862897/500000000 : ℝ)^1097 ≤ (15912631264313/50000000000000 : ℝ)^841 := by
    have hnat : (207862897 : ℕ)^1097*50000000000000^841 ≤ 15912631264313^841*500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207862897 500000000 15912631264313 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438196771/1000000000 : ℝ)^1097 ≤ (8521841420973/25000000000000 : ℝ)^841 := by
    have hnat : (438196771 : ℕ)^1097*25000000000000^841 ≤ 8521841420973^841*1000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438196771 1000000000 8521841420973 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4381968311/10000000000 : ℝ)^1097 ≤ (170436858911/500000000000 : ℝ)^841 := by
    have hnat : (4381968311 : ℕ)^1097*500000000000^841 ≤ 170436858911^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381968311 10000000000 170436858911 500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207862897/500000000 : ℝ), (438196771/1000000000 : ℝ), (4381968311/10000000000 : ℝ)] ![(15912631264313/50000000000000 : ℝ), (8521841420973/25000000000000 : ℝ), (170436858911/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207862897/500000000 : ℝ)|^1097 ≤ (15912631264313/50000000000000 : ℝ)^841
        have hw : |(207862897/500000000 : ℝ)|=(207862897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(438196771/1000000000 : ℝ)|^1097 ≤ (8521841420973/25000000000000 : ℝ)^841
        have hw : |(438196771/1000000000 : ℝ)|=(438196771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4381968311/10000000000 : ℝ)|^1097 ≤ (170436858911/500000000000 : ℝ)^841
        have hw : |(4381968311/10000000000 : ℝ)|=(4381968311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_8 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033565183/5000000000 : ℝ)*x 0 + (2591828143/5000000000 : ℝ)*x 1 + (2700137323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033565183/5000000000 : ℝ)^1097 ≤ (12792816518879/100000000000000 : ℝ)^841 := by
    have hnat : (1033565183 : ℕ)^1097*100000000000000^841 ≤ 12792816518879^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033565183 5000000000 12792816518879 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591828143/5000000000 : ℝ)^1097 ≤ (10609907550539/25000000000000 : ℝ)^841 := by
    have hnat : (2591828143 : ℕ)^1097*25000000000000^841 ≤ 10609907550539^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591828143 5000000000 10609907550539 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700137323/5000000000 : ℝ)^1097 ≤ (22383776628259/50000000000000 : ℝ)^841 := by
    have hnat : (2700137323 : ℕ)^1097*50000000000000^841 ≤ 22383776628259^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700137323 5000000000 22383776628259 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033565183/5000000000 : ℝ), (2591828143/5000000000 : ℝ), (2700137323/5000000000 : ℝ)] ![(12792816518879/100000000000000 : ℝ), (10609907550539/25000000000000 : ℝ), (22383776628259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033565183/5000000000 : ℝ)|^1097 ≤ (12792816518879/100000000000000 : ℝ)^841
        have hw : |(-1033565183/5000000000 : ℝ)|=(1033565183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591828143/5000000000 : ℝ)|^1097 ≤ (10609907550539/25000000000000 : ℝ)^841
        have hw : |(2591828143/5000000000 : ℝ)|=(2591828143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700137323/5000000000 : ℝ)|^1097 ≤ (22383776628259/50000000000000 : ℝ)^841
        have hw : |(2700137323/5000000000 : ℝ)|=(2700137323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_9 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (659533971/1250000000 : ℝ)*x 0 + (-1943126629/10000000000 : ℝ)*x 1 + (5400274437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659533971/1250000000 : ℝ)^1097 ≤ (868627693149/2000000000000 : ℝ)^841 := by
    have hnat : (659533971 : ℕ)^1097*2000000000000^841 ≤ 868627693149^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659533971 1250000000 868627693149 2000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1943126629/10000000000 : ℝ)^1097 ≤ (5900532164721/50000000000000 : ℝ)^841 := by
    have hnat : (1943126629 : ℕ)^1097*50000000000000^841 ≤ 5900532164721^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943126629 10000000000 5900532164721 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400274437/10000000000 : ℝ)^1097 ≤ (22383775498269/50000000000000 : ℝ)^841 := by
    have hnat : (5400274437 : ℕ)^1097*50000000000000^841 ≤ 22383775498269^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400274437 10000000000 22383775498269 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659533971/1250000000 : ℝ), (-1943126629/10000000000 : ℝ), (5400274437/10000000000 : ℝ)] ![(868627693149/2000000000000 : ℝ), (5900532164721/50000000000000 : ℝ), (22383775498269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659533971/1250000000 : ℝ)|^1097 ≤ (868627693149/2000000000000 : ℝ)^841
        have hw : |(659533971/1250000000 : ℝ)|=(659533971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1943126629/10000000000 : ℝ)|^1097 ≤ (5900532164721/50000000000000 : ℝ)^841
        have hw : |(-1943126629/10000000000 : ℝ)|=(1943126629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400274437/10000000000 : ℝ)|^1097 ≤ (22383775498269/50000000000000 : ℝ)^841
        have hw : |(5400274437/10000000000 : ℝ)|=(5400274437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_10 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5276271661/10000000000 : ℝ)*x 0 + (2700137201/5000000000 : ℝ)*x 1 + (-971563411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276271661/10000000000 : ℝ)^1097 ≤ (2171569175429/5000000000000 : ℝ)^841 := by
    have hnat : (5276271661 : ℕ)^1097*5000000000000^841 ≤ 2171569175429^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276271661 10000000000 2171569175429 5000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700137201/5000000000 : ℝ)^1097 ≤ (44767550618073/100000000000000 : ℝ)^841 := by
    have hnat : (2700137201 : ℕ)^1097*100000000000000^841 ≤ 44767550618073^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700137201 5000000000 44767550618073 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971563411/5000000000 : ℝ)^1097 ≤ (5900532929187/50000000000000 : ℝ)^841 := by
    have hnat : (971563411 : ℕ)^1097*50000000000000^841 ≤ 5900532929187^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971563411 5000000000 5900532929187 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276271661/10000000000 : ℝ), (2700137201/5000000000 : ℝ), (-971563411/5000000000 : ℝ)] ![(2171569175429/5000000000000 : ℝ), (44767550618073/100000000000000 : ℝ), (5900532929187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276271661/10000000000 : ℝ)|^1097 ≤ (2171569175429/5000000000000 : ℝ)^841
        have hw : |(5276271661/10000000000 : ℝ)|=(5276271661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700137201/5000000000 : ℝ)|^1097 ≤ (44767550618073/100000000000000 : ℝ)^841
        have hw : |(2700137201/5000000000 : ℝ)|=(2700137201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-971563411/5000000000 : ℝ)|^1097 ≤ (5900532929187/50000000000000 : ℝ)^841
        have hw : |(-971563411/5000000000 : ℝ)|=(971563411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_11 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4484649593/10000000000 : ℝ)*x 0 + (4218035679/10000000000 : ℝ)*x 1 + (4218036333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4484649593/10000000000 : ℝ)^1097 ≤ (8783242015361/25000000000000 : ℝ)^841 := by
    have hnat : (4484649593 : ℕ)^1097*25000000000000^841 ≤ 8783242015361^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484649593 10000000000 8783242015361 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4218035679/10000000000 : ℝ)^1097 ≤ (32433512680699/100000000000000 : ℝ)^841 := by
    have hnat : (4218035679 : ℕ)^1097*100000000000000^841 ≤ 32433512680699^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218035679 10000000000 32433512680699 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4218036333/10000000000 : ℝ)^1097 ≤ (1621675962011/5000000000000 : ℝ)^841 := by
    have hnat : (4218036333 : ℕ)^1097*5000000000000^841 ≤ 1621675962011^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218036333 10000000000 1621675962011 5000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4484649593/10000000000 : ℝ), (4218035679/10000000000 : ℝ), (4218036333/10000000000 : ℝ)] ![(8783242015361/25000000000000 : ℝ), (32433512680699/100000000000000 : ℝ), (1621675962011/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4484649593/10000000000 : ℝ)|^1097 ≤ (8783242015361/25000000000000 : ℝ)^841
        have hw : |(4484649593/10000000000 : ℝ)|=(4484649593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4218035679/10000000000 : ℝ)|^1097 ≤ (32433512680699/100000000000000 : ℝ)^841
        have hw : |(4218035679/10000000000 : ℝ)|=(4218035679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4218036333/10000000000 : ℝ)|^1097 ≤ (1621675962011/5000000000000 : ℝ)^841
        have hw : |(4218036333/10000000000 : ℝ)|=(4218036333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_12 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-375935333/2000000000 : ℝ)*x 0 + (5467127381/10000000000 : ℝ)*x 1 + (1051076959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375935333/2000000000 : ℝ)^1097 ≤ (11300935757071/100000000000000 : ℝ)^841 := by
    have hnat : (375935333 : ℕ)^1097*100000000000000^841 ≤ 11300935757071^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375935333 2000000000 11300935757071 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467127381/10000000000 : ℝ)^1097 ≤ (45491809920169/100000000000000 : ℝ)^841 := by
    have hnat : (5467127381 : ℕ)^1097*100000000000000^841 ≤ 45491809920169^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467127381 10000000000 45491809920169 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051076959/2000000000 : ℝ)^1097 ≤ (4320725430681/10000000000000 : ℝ)^841 := by
    have hnat : (1051076959 : ℕ)^1097*10000000000000^841 ≤ 4320725430681^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051076959 2000000000 4320725430681 10000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375935333/2000000000 : ℝ), (5467127381/10000000000 : ℝ), (1051076959/2000000000 : ℝ)] ![(11300935757071/100000000000000 : ℝ), (45491809920169/100000000000000 : ℝ), (4320725430681/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375935333/2000000000 : ℝ)|^1097 ≤ (11300935757071/100000000000000 : ℝ)^841
        have hw : |(-375935333/2000000000 : ℝ)|=(375935333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467127381/10000000000 : ℝ)|^1097 ≤ (45491809920169/100000000000000 : ℝ)^841
        have hw : |(5467127381/10000000000 : ℝ)|=(5467127381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051076959/2000000000 : ℝ)|^1097 ≤ (4320725430681/10000000000000 : ℝ)^841
        have hw : |(1051076959/2000000000 : ℝ)|=(1051076959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_13 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5377679619/10000000000 : ℝ)*x 0 + (-400394481/2000000000 : ℝ)*x 1 + (5255384189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377679619/10000000000 : ℝ)^1097 ≤ (445233822537/1000000000000 : ℝ)^841 := by
    have hnat : (5377679619 : ℕ)^1097*1000000000000^841 ≤ 445233822537^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377679619 10000000000 445233822537 1000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400394481/2000000000 : ℝ)^1097 ≤ (2453873985271/20000000000000 : ℝ)^841 := by
    have hnat : (400394481 : ℕ)^1097*20000000000000^841 ≤ 2453873985271^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400394481 2000000000 2453873985271 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255384189/10000000000 : ℝ)^1097 ≤ (43207247807977/100000000000000 : ℝ)^841 := by
    have hnat : (5255384189 : ℕ)^1097*100000000000000^841 ≤ 43207247807977^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255384189 10000000000 43207247807977 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377679619/10000000000 : ℝ), (-400394481/2000000000 : ℝ), (5255384189/10000000000 : ℝ)] ![(445233822537/1000000000000 : ℝ), (2453873985271/20000000000000 : ℝ), (43207247807977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377679619/10000000000 : ℝ)|^1097 ≤ (445233822537/1000000000000 : ℝ)^841
        have hw : |(5377679619/10000000000 : ℝ)|=(5377679619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-400394481/2000000000 : ℝ)|^1097 ≤ (2453873985271/20000000000000 : ℝ)^841
        have hw : |(-400394481/2000000000 : ℝ)|=(400394481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255384189/10000000000 : ℝ)|^1097 ≤ (43207247807977/100000000000000 : ℝ)^841
        have hw : |(5255384189/10000000000 : ℝ)|=(5255384189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_14 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5377680009/10000000000 : ℝ)*x 0 + (1313846057/2500000000 : ℝ)*x 1 + (-1000985913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377680009/10000000000 : ℝ)^1097 ≤ (44523386465507/100000000000000 : ℝ)^841 := by
    have hnat : (5377680009 : ℕ)^1097*100000000000000^841 ≤ 44523386465507^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377680009 10000000000 44523386465507 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313846057/2500000000 : ℝ)^1097 ≤ (43207248226219/100000000000000 : ℝ)^841 := by
    have hnat : (1313846057 : ℕ)^1097*100000000000000^841 ≤ 43207248226219^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313846057 2500000000 43207248226219 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000985913/5000000000 : ℝ)^1097 ≤ (3067341324429/25000000000000 : ℝ)^841 := by
    have hnat : (1000985913 : ℕ)^1097*25000000000000^841 ≤ 3067341324429^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000985913 5000000000 3067341324429 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377680009/10000000000 : ℝ), (1313846057/2500000000 : ℝ), (-1000985913/5000000000 : ℝ)] ![(44523386465507/100000000000000 : ℝ), (43207248226219/100000000000000 : ℝ), (3067341324429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377680009/10000000000 : ℝ)|^1097 ≤ (44523386465507/100000000000000 : ℝ)^841
        have hw : |(5377680009/10000000000 : ℝ)|=(5377680009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313846057/2500000000 : ℝ)|^1097 ≤ (43207248226219/100000000000000 : ℝ)^841
        have hw : |(1313846057/2500000000 : ℝ)|=(1313846057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000985913/5000000000 : ℝ)|^1097 ≤ (3067341324429/25000000000000 : ℝ)^841
        have hw : |(-1000985913/5000000000 : ℝ)|=(1000985913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_box_15 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4129531467/10000000000 : ℝ)*x 0 + (1098897801/2500000000 : ℝ)*x 1 + (4395589911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4129531467/10000000000 : ℝ)^1097 ≤ (15774338794133/50000000000000 : ℝ)^841 := by
    have hnat : (4129531467 : ℕ)^1097*50000000000000^841 ≤ 15774338794133^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129531467 10000000000 15774338794133 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098897801/2500000000 : ℝ)^1097 ≤ (34225667763187/100000000000000 : ℝ)^841 := by
    have hnat : (1098897801 : ℕ)^1097*100000000000000^841 ≤ 34225667763187^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098897801 2500000000 34225667763187 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4395589911/10000000000 : ℝ)^1097 ≤ (34225654630797/100000000000000 : ℝ)^841 := by
    have hnat : (4395589911 : ℕ)^1097*100000000000000^841 ≤ 34225654630797^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395589911 10000000000 34225654630797 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4129531467/10000000000 : ℝ), (1098897801/2500000000 : ℝ), (4395589911/10000000000 : ℝ)] ![(15774338794133/50000000000000 : ℝ), (34225667763187/100000000000000 : ℝ), (34225654630797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4129531467/10000000000 : ℝ)|^1097 ≤ (15774338794133/50000000000000 : ℝ)^841
        have hw : |(4129531467/10000000000 : ℝ)|=(4129531467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098897801/2500000000 : ℝ)|^1097 ≤ (34225667763187/100000000000000 : ℝ)^841
        have hw : |(1098897801/2500000000 : ℝ)|=(1098897801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4395589911/10000000000 : ℝ)|^1097 ≤ (34225654630797/100000000000000 : ℝ)^841
        have hw : |(4395589911/10000000000 : ℝ)|=(4395589911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1428_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62899/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59111/100000 : ℝ) ∧ (80443/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84681/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5669/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5669/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5669/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5669/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5669/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5669/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5669/50000 : ℝ) ^ (4387/1024 : ℝ) ≤ (8901522116037499/100000000000000000000 : ℝ) := by
    have hpowers : (5669/50000 : ℝ)^4387 ≤ (8901522116037499/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5669 : ℕ)^4387*100000000000000000000^1024 ≤ 8901522116037499^1024*50000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5669 50000 8901522116037499 100000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5669/50000 : ℝ)) (X := (8901522116037499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3689/25000 : ℝ) ^ (4387/1024 : ℝ) ≤ (5504810225402887/20000000000000000000 : ℝ) := by
    have hpowers : (3689/25000 : ℝ)^4387 ≤ (5504810225402887/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3689 : ℕ)^4387*20000000000000000000^1024 ≤ 5504810225402887^1024*25000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3689 25000 5504810225402887 20000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3689/25000 : ℝ)) (X := (5504810225402887/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008901522116037499/50000000000000000000 : ℝ) ≤ (5000207762405193/5000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (50008901522116037499/50000000000000000000 : ℝ)^1024 ≤ (5000207762405193/5000000000000000 : ℝ)^4387 := by
      have hnat : (50008901522116037499 : ℕ)^1024*5000000000000000^4387 ≤ 5000207762405193^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008901522116037499 50000000000000000000 5000207762405193 5000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000207762405193/5000000000000000 : ℝ)) (X := (50008901522116037499/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018212786621525967/50000000000000000000 : ℝ) ≤ (5000425057903639/5000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (50018212786621525967/50000000000000000000 : ℝ)^1024 ≤ (5000425057903639/5000000000000000 : ℝ)^4387 := by
      have hnat : (50018212786621525967 : ℕ)^1024*5000000000000000^4387 ≤ 5000425057903639^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018212786621525967 50000000000000000000 5000425057903639 5000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000425057903639/5000000000000000 : ℝ)) (X := (50018212786621525967/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005504810225402887/10000000000000000000 : ℝ) ≤ (1000128470680417/1000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (10005504810225402887/10000000000000000000 : ℝ)^1024 ≤ (1000128470680417/1000000000000000 : ℝ)^4387 := by
      have hnat : (10005504810225402887 : ℕ)^1024*1000000000000000^4387 ≤ 1000128470680417^4387*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005504810225402887 10000000000000000000 1000128470680417 1000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000128470680417/1000000000000000 : ℝ)) (X := (10005504810225402887/10000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8901522116037499/100000000000000000000 : ℝ) ≤ ((8542891369589094089/8545000000000000000 : ℝ)+2*(108647749223/85450000000000 : ℝ)*(5669/50000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (8542891369589094089/8545000000000000000 : ℝ)+2*(108647749223/85450000000000 : ℝ)*(5669/50000 : ℝ)=(5000207762405193/5000000000000000 : ℝ) by norm_num, show 1+2*(8901522116037499/100000000000000000000 : ℝ)=(50008901522116037499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5504810225402887/20000000000000000000 : ℝ)+(8901522116037499/100000000000000000000 : ℝ) ≤ ((8542891369589094089/8545000000000000000 : ℝ)+(108647749223/85450000000000 : ℝ)*((3689/25000 : ℝ)+(5669/50000 : ℝ)))^(4387/1024 : ℝ) := by
    rw [show (8542891369589094089/8545000000000000000 : ℝ)+(108647749223/85450000000000 : ℝ)*((3689/25000 : ℝ)+(5669/50000 : ℝ))=(5000425057903639/5000000000000000 : ℝ) by norm_num, show 1+(5504810225402887/20000000000000000000 : ℝ)+(8901522116037499/100000000000000000000 : ℝ)=(50018212786621525967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5504810225402887/20000000000000000000 : ℝ) ≤ ((8542891369589094089/8545000000000000000 : ℝ)+2*(108647749223/85450000000000 : ℝ)*(3689/25000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (8542891369589094089/8545000000000000000 : ℝ)+2*(108647749223/85450000000000 : ℝ)*(3689/25000 : ℝ)=(1000128470680417/1000000000000000 : ℝ) by norm_num, show 1+2*(5504810225402887/20000000000000000000 : ℝ)=(10005504810225402887/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8542891369589094089/8545000000000000000 : ℝ)*(X 1 0+X 2 0)+(108647749223/85450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (8542891369589094089/8545000000000000000 : ℝ)) (alpha := (108647749223/85450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8542891369589094089/8545000000000000000 : ℝ)*(X 0 1+X 2 1)+(108647749223/85450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (8542891369589094089/8545000000000000000 : ℝ)) (alpha := (108647749223/85450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8542891369589094089/8545000000000000000 : ℝ)*(X 0 2+X 1 2)+(108647749223/85450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (8542891369589094089/8545000000000000000 : ℝ)) (alpha := (108647749223/85450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1811209499/10000000000 : ℝ)*X 0 0+(1346574887/2500000000 : ℝ)*X 0 1+(673287539/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2643028129/5000000000 : ℝ)*X 1 0+(-974463159/5000000000 : ℝ)*X 1 1+(5386299807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2643028281/5000000000 : ℝ)*X 2 0+(673287463/1250000000 : ℝ)*X 2 1+(-974463023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((445094437/1000000000 : ℝ)*X 0 0+(1058793959/2500000000 : ℝ)*X 0 1+(2117587803/5000000000 : ℝ)*X 0 2+(445094437/1000000000 : ℝ)*X 1 0+(1058793959/2500000000 : ℝ)*X 1 1+(2117587803/5000000000 : ℝ)*X 1 2+(445094437/1000000000 : ℝ)*X 2 0+(1058793959/2500000000 : ℝ)*X 2 1+(2117587803/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2135415227/10000000000 : ℝ)*X 0 0+(32915687/62500000 : ℝ)*X 0 1+(5266510097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5369895099/10000000000 : ℝ)*X 1 0+(-1997555513/10000000000 : ℝ)*X 1 1+(1316627379/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1342473611/2500000000 : ℝ)*X 2 0+(2633255359/5000000000 : ℝ)*X 2 1+(-62423587/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((207862897/500000000 : ℝ)*X 0 0+(438196771/1000000000 : ℝ)*X 0 1+(4381968311/10000000000 : ℝ)*X 0 2+(207862897/500000000 : ℝ)*X 1 0+(438196771/1000000000 : ℝ)*X 1 1+(4381968311/10000000000 : ℝ)*X 1 2+(207862897/500000000 : ℝ)*X 2 0+(438196771/1000000000 : ℝ)*X 2 1+(4381968311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1033565183/5000000000 : ℝ)*X 0 0+(2591828143/5000000000 : ℝ)*X 0 1+(2700137323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((659533971/1250000000 : ℝ)*X 1 0+(-1943126629/10000000000 : ℝ)*X 1 1+(5400274437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276271661/10000000000 : ℝ)*X 2 0+(2700137201/5000000000 : ℝ)*X 2 1+(-971563411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4484649593/10000000000 : ℝ)*X 0 0+(4218035679/10000000000 : ℝ)*X 0 1+(4218036333/10000000000 : ℝ)*X 0 2+(4484649593/10000000000 : ℝ)*X 1 0+(4218035679/10000000000 : ℝ)*X 1 1+(4218036333/10000000000 : ℝ)*X 1 2+(4484649593/10000000000 : ℝ)*X 2 0+(4218035679/10000000000 : ℝ)*X 2 1+(4218036333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-375935333/2000000000 : ℝ)*X 0 0+(5467127381/10000000000 : ℝ)*X 0 1+(1051076959/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5377679619/10000000000 : ℝ)*X 1 0+(-400394481/2000000000 : ℝ)*X 1 1+(5255384189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5377680009/10000000000 : ℝ)*X 2 0+(1313846057/2500000000 : ℝ)*X 2 1+(-1000985913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4129531467/10000000000 : ℝ)*X 0 0+(1098897801/2500000000 : ℝ)*X 0 1+(4395589911/10000000000 : ℝ)*X 0 2+(4129531467/10000000000 : ℝ)*X 1 0+(1098897801/2500000000 : ℝ)*X 1 1+(4395589911/10000000000 : ℝ)*X 1 2+(4129531467/10000000000 : ℝ)*X 2 0+(1098897801/2500000000 : ℝ)*X 2 1+(4395589911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62899/100000 : ℝ) ≤ (-67181174086747820102550100697421/106812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16187969/25000000000000 : ℝ)*(lower1) + (99963963/100000000000000 : ℝ)*(lower2) + (81367281/50000000000000 : ℝ)*(lower3) + (20016533/50000000000000 : ℝ)*(lower4) + (753913180452879/25000000000000 : ℝ)*(major0) + (753913180452879/25000000000000 : ℝ)*(major1) + (753913180452879/25000000000000 : ℝ)*(major2) + (11925118627/100000000000000 : ℝ)*(sp1) + (2072581997977221/50000000000000 : ℝ)*(sp4) + (518144008854477/12500000000000 : ℝ)*(sp5) + (165794668070433/4000000000000 : ℝ)*(sp6) + (1907074395480341/100000000000000 : ℝ)*(sp7) + (297294193617/100000000000000 : ℝ)*(sp14) + (16252692403/50000000000000 : ℝ)*(sp15) + (953553450432573/50000000000000 : ℝ)*(f.failure) + (2072581997977221/50000000000000 : ℝ)*(f.sum) + (4776200184139/534062500000000000000000000 : ℝ)*base66 + (2279903706007117769/213625000000000000000000000000000 : ℝ)*base68 + (590315172513742769/213625000000000000000000000000000 : ℝ)*base70 + (3665631683814867769/213625000000000000000000000000000 : ℝ)*base72 + (3462958057541/2136250000000000000000000000 : ℝ)*base74 + (3614140554168617769/213625000000000000000000000000000 : ℝ)*base76 + (3726060920418242769/213625000000000000000000000000000 : ℝ)*base78 + (1518123447216367769/213625000000000000000000000000000 : ℝ)*base80 + (1859252302739/8545000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5716431/2500000000000000000000 : ℝ)*base89 + (5716431/2500000000000000000000 : ℝ)*base91 + (5716431/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (59111/100000 : ℝ) ≤ (126281495043887888156958092721453/213625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42858269/100000000000000 : ℝ)*(lower3) + (37282207/25000000000000 : ℝ)*(upper4) + (55481/400000000000 : ℝ)*(upper5) + (3087230621101841/100000000000000 : ℝ)*(major0) + (3087230621101841/100000000000000 : ℝ)*(major1) + (3087230621101841/100000000000000 : ℝ)*(major2) + (4202374743737481/100000000000000 : ℝ)*(sp0) + (131323338711931/3125000000000 : ℝ)*(sp1) + (52529608582567/1250000000000 : ℝ)*(sp2) + (488093185713967/25000000000000 : ℝ)*(sp3) + (107121353/50000000000000 : ℝ)*(sp7) + (36902528667/100000000000000 : ℝ)*(sp9) + (15054705099/100000000000000 : ℝ)*(sp10) + (8997572979/100000000000000 : ℝ)*(sp12) + (1952372957098573/100000000000000 : ℝ)*(f.failure) + (210119187065523/5000000000000 : ℝ)*(f.sum) + (10288169820121/2136250000000000000000000000 : ℝ)*base66 + (2543740801323082151/854500000000000000000000000000000 : ℝ)*base68 + (77635803024917849/854500000000000000000000000000000 : ℝ)*base69 + (4759456307190417849/854500000000000000000000000000000 : ℝ)*base71 + (27622284995319/8545000000000000000000000000 : ℝ)*base74 + (2018503313317917849/854500000000000000000000000000000 : ℝ)*base75 + (3821690266488917849/854500000000000000000000000000000 : ℝ)*base77 + (6561988378397417849/854500000000000000000000000000000 : ℝ)*base79 + (26971810240267/4272500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (39981569/5000000000000000000000 : ℝ)*base90 + (39981569/5000000000000000000000 : ℝ)*base92 + (39981569/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80443/100000 : ℝ) ≤ (171851589468844116579173334157989/213625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158292641/100000000000000 : ℝ)*(upper0) + (62527621/100000000000000 : ℝ)*(upper2) + (3967503/4000000000000 : ℝ)*(lower5) + (3395180116026633/100000000000000 : ℝ)*(major0) + (3395180116026633/100000000000000 : ℝ)*(major1) + (3395180116026633/100000000000000 : ℝ)*(major2) + (7971751733/100000000000000 : ℝ)*(sp0) + (6710561321/50000000000000 : ℝ)*(sp1) + (39593040729/100000000000000 : ℝ)*(sp3) + (230820443963089/5000000000000 : ℝ)*(sp8) + (4616410614575769/100000000000000 : ℝ)*(sp9) + (1154106008924603/25000000000000 : ℝ)*(sp10) + (536770363449211/25000000000000 : ℝ)*(sp11) + (3592342449/50000000000000 : ℝ)*(sp12) + (2147121046837573/100000000000000 : ℝ)*(f.failure) + (1154106008924603/25000000000000 : ℝ)*(f.sum) + (45238523188593/8545000000000000000000000000 : ℝ)*base65 + (506341740183772337/854500000000000000000000000000000 : ℝ)*base67 + (693215002678772337/854500000000000000000000000000000 : ℝ)*base69 + (7810749563257772337/854500000000000000000000000000000 : ℝ)*base71 + (5255375973017/8545000000000000000000000000 : ℝ)*base74 + (1489907512854272337/854500000000000000000000000000000 : ℝ)*base75 + (5095901288889772337/854500000000000000000000000000000 : ℝ)*base77 + (895031186265227663/854500000000000000000000000000000 : ℝ)*base80 + (3247805001743/2136250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (4251431/5000000000000000000000 : ℝ)*base89 + (4251431/5000000000000000000000 : ℝ)*base91 + (4251431/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84681/100000 : ℝ) ≤ (-45223647087415559160476275375791/53406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41147957/100000000000000 : ℝ)*(lower0) + (48373379/12500000000000 : ℝ)*(lower2) + (81143799/100000000000000 : ℝ)*(upper3) + (858161728234027/25000000000000 : ℝ)*(major0) + (858161728234027/25000000000000 : ℝ)*(major1) + (858161728234027/25000000000000 : ℝ)*(major2) + (260746853/100000000000000 : ℝ)*(sp0) + (166625796623/50000000000000 : ℝ)*(sp5) + (72722824141/100000000000000 : ℝ)*(sp6) + (57244875161/50000000000000 : ℝ)*(sp7) + (2361352301990247/50000000000000 : ℝ)*(sp12) + (4722371613134101/100000000000000 : ℝ)*(sp13) + (2361316070951603/50000000000000 : ℝ)*(sp14) + (217070066033149/10000000000000 : ℝ)*(sp15) + (542703787520453/25000000000000 : ℝ)*(f.failure) + (4722704864727347/100000000000000 : ℝ)*(f.sum) + (43480922236783/8545000000000000000000000000 : ℝ)*base65 + (1281012357651283597/213625000000000000000000000000000 : ℝ)*base68 + (1488571509956283597/213625000000000000000000000000000 : ℝ)*base70 + (917421784126908597/213625000000000000000000000000000 : ℝ)*base72 + (25503565652203/8545000000000000000000000000 : ℝ)*base73 + (1711030151297658597/213625000000000000000000000000000 : ℝ)*base76 + (29857137402466403/213625000000000000000000000000000 : ℝ)*base77 + (1649953317342783597/213625000000000000000000000000000 : ℝ)*base80 + (659825447659/1068125000000000000000000000 : ℝ)*base82 + (773209/1250000000000000000000 : ℝ)*base90 + (773209/1250000000000000000000 : ℝ)*base92 + (773209/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1428_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62899/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59111/100000 : ℝ) else (80443/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84681/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1428_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1428_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62899/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59111/100000 : ℝ) else (80443/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84681/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1428_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1428_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1428_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62899/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59111/100000 : ℝ) else (80443/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84681/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1428_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
