-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1562_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:24:42.329053+00:00
-- url     : https://prove2.me/submissions/d277ea9f-33f1-48e6-a1d0-09ff163ca573

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
theorem support_rectangle_w1562_s3_0 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-71853119/400000000 : ℝ)*x 0 + (1357160031/2500000000 : ℝ)*x 1 + (652266349/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71853119/400000000 : ℝ)^4621 ≤ (11018510338857/100000000000000 : ℝ)^3597 := by
    have hnat : (71853119 : ℕ)^4621*100000000000000^3597 ≤ 11018510338857^3597*400000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71853119 400000000 11018510338857 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357160031/2500000000 : ℝ)^4621 ≤ (45620753659057/100000000000000 : ℝ)^3597 := by
    have hnat : (1357160031 : ℕ)^4621*100000000000000^3597 ≤ 45620753659057^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357160031 2500000000 45620753659057 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652266349/1250000000 : ℝ)^4621 ≤ (43360735979859/100000000000000 : ℝ)^3597 := by
    have hnat : (652266349 : ℕ)^4621*100000000000000^3597 ≤ 43360735979859^3597*1250000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652266349 1250000000 43360735979859 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-71853119/400000000 : ℝ), (1357160031/2500000000 : ℝ), (652266349/1250000000 : ℝ)] ![(11018510338857/100000000000000 : ℝ), (45620753659057/100000000000000 : ℝ), (43360735979859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-71853119/400000000 : ℝ)|^4621 ≤ (11018510338857/100000000000000 : ℝ)^3597
        have hw : |(-71853119/400000000 : ℝ)|=(71853119/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357160031/2500000000 : ℝ)|^4621 ≤ (45620753659057/100000000000000 : ℝ)^3597
        have hw : |(1357160031/2500000000 : ℝ)|=(1357160031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652266349/1250000000 : ℝ)|^4621 ≤ (43360735979859/100000000000000 : ℝ)^3597
        have hw : |(652266349/1250000000 : ℝ)|=(652266349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s3_1 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349164431/10000000000 : ℝ)*x 0 + (-1904078119/10000000000 : ℝ)*x 1 + (5218130873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349164431/10000000000 : ℝ)^4621 ≤ (8952904073597/20000000000000 : ℝ)^3597 := by
    have hnat : (5349164431 : ℕ)^4621*20000000000000^3597 ≤ 8952904073597^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349164431 10000000000 8952904073597 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904078119/10000000000 : ℝ)^4621 ≤ (2374948554879/20000000000000 : ℝ)^3597 := by
    have hnat : (1904078119 : ℕ)^4621*20000000000000^3597 ≤ 2374948554879^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904078119 10000000000 2374948554879 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218130873/10000000000 : ℝ)^4621 ≤ (43360736844553/100000000000000 : ℝ)^3597 := by
    have hnat : (5218130873 : ℕ)^4621*100000000000000^3597 ≤ 43360736844553^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218130873 10000000000 43360736844553 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349164431/10000000000 : ℝ), (-1904078119/10000000000 : ℝ), (5218130873/10000000000 : ℝ)] ![(8952904073597/20000000000000 : ℝ), (2374948554879/20000000000000 : ℝ), (43360736844553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349164431/10000000000 : ℝ)|^4621 ≤ (8952904073597/20000000000000 : ℝ)^3597
        have hw : |(5349164431/10000000000 : ℝ)|=(5349164431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1904078119/10000000000 : ℝ)|^4621 ≤ (2374948554879/20000000000000 : ℝ)^3597
        have hw : |(-1904078119/10000000000 : ℝ)|=(1904078119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218130873/10000000000 : ℝ)|^4621 ≤ (43360736844553/100000000000000 : ℝ)^3597
        have hw : |(5218130873/10000000000 : ℝ)|=(5218130873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s3_2 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334322759/625000000 : ℝ)*x 0 + (208725241/400000000 : ℝ)*x 1 + (-1904078303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334322759/625000000 : ℝ)^4621 ≤ (22382258641243/50000000000000 : ℝ)^3597 := by
    have hnat : (334322759 : ℕ)^4621*50000000000000^3597 ≤ 22382258641243^3597*625000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334322759 625000000 22382258641243 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208725241/400000000 : ℝ)^4621 ≤ (43360738467187/100000000000000 : ℝ)^3597 := by
    have hnat : (208725241 : ℕ)^4621*100000000000000^3597 ≤ 43360738467187^3597*400000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208725241 400000000 43360738467187 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904078303/10000000000 : ℝ)^4621 ≤ (5937372124291/50000000000000 : ℝ)^3597 := by
    have hnat : (1904078303 : ℕ)^4621*50000000000000^3597 ≤ 5937372124291^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904078303 10000000000 5937372124291 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334322759/625000000 : ℝ), (208725241/400000000 : ℝ), (-1904078303/10000000000 : ℝ)] ![(22382258641243/50000000000000 : ℝ), (43360738467187/100000000000000 : ℝ), (5937372124291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334322759/625000000 : ℝ)|^4621 ≤ (22382258641243/50000000000000 : ℝ)^3597
        have hw : |(334322759/625000000 : ℝ)|=(334322759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208725241/400000000 : ℝ)|^4621 ≤ (43360738467187/100000000000000 : ℝ)^3597
        have hw : |(208725241/400000000 : ℝ)|=(208725241/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1904078303/10000000000 : ℝ)|^4621 ≤ (5937372124291/50000000000000 : ℝ)^3597
        have hw : |(-1904078303/10000000000 : ℝ)|=(1904078303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s3_3 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4246869347/10000000000 : ℝ)*x 0 + (2002810797/5000000000 : ℝ)*x 1 + (562479347/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4246869347/10000000000 : ℝ)^4621 ≤ (33280276843377/100000000000000 : ℝ)^3597 := by
    have hnat : (4246869347 : ℕ)^4621*100000000000000^3597 ≤ 33280276843377^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246869347 10000000000 33280276843377 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002810797/5000000000 : ℝ)^4621 ≤ (15435735551021/50000000000000 : ℝ)^3597 := by
    have hnat : (2002810797 : ℕ)^4621*50000000000000^3597 ≤ 15435735551021^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002810797 5000000000 15435735551021 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562479347/1250000000 : ℝ)^4621 ≤ (8962063009193/25000000000000 : ℝ)^3597 := by
    have hnat : (562479347 : ℕ)^4621*25000000000000^3597 ≤ 8962063009193^3597*1250000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562479347 1250000000 8962063009193 25000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4246869347/10000000000 : ℝ), (2002810797/5000000000 : ℝ), (562479347/1250000000 : ℝ)] ![(33280276843377/100000000000000 : ℝ), (15435735551021/50000000000000 : ℝ), (8962063009193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4246869347/10000000000 : ℝ)|^4621 ≤ (33280276843377/100000000000000 : ℝ)^3597
        have hw : |(4246869347/10000000000 : ℝ)|=(4246869347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2002810797/5000000000 : ℝ)|^4621 ≤ (15435735551021/50000000000000 : ℝ)^3597
        have hw : |(2002810797/5000000000 : ℝ)|=(2002810797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562479347/1250000000 : ℝ)|^4621 ≤ (8962063009193/25000000000000 : ℝ)^3597
        have hw : |(562479347/1250000000 : ℝ)|=(562479347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s3_4 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1796356467/10000000000 : ℝ)*x 0 + (5219243799/10000000000 : ℝ)*x 1 + (1356879679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1796356467/10000000000 : ℝ)^4621 ≤ (11018734859717/100000000000000 : ℝ)^3597 := by
    have hnat : (1796356467 : ℕ)^4621*100000000000000^3597 ≤ 11018734859717^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796356467 10000000000 11018734859717 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219243799/10000000000 : ℝ)^4621 ≤ (8674523589119/20000000000000 : ℝ)^3597 := by
    have hnat : (5219243799 : ℕ)^4621*20000000000000^3597 ≤ 8674523589119^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219243799 10000000000 8674523589119 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356879679/2500000000 : ℝ)^4621 ≤ (22804323590583/50000000000000 : ℝ)^3597 := by
    have hnat : (1356879679 : ℕ)^4621*50000000000000^3597 ≤ 22804323590583^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356879679 2500000000 22804323590583 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1796356467/10000000000 : ℝ), (5219243799/10000000000 : ℝ), (1356879679/2500000000 : ℝ)] ![(11018734859717/100000000000000 : ℝ), (8674523589119/20000000000000 : ℝ), (22804323590583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1796356467/10000000000 : ℝ)|^4621 ≤ (11018734859717/100000000000000 : ℝ)^3597
        have hw : |(-1796356467/10000000000 : ℝ)|=(1796356467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219243799/10000000000 : ℝ)|^4621 ≤ (8674523589119/20000000000000 : ℝ)^3597
        have hw : |(5219243799/10000000000 : ℝ)|=(5219243799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356879679/2500000000 : ℝ)|^4621 ≤ (22804323590583/50000000000000 : ℝ)^3597
        have hw : |(1356879679/2500000000 : ℝ)|=(1356879679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s3_5 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293523443/10000000000 : ℝ)*x 0 + (-847345229/5000000000 : ℝ)*x 1 + (5427518649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293523443/10000000000 : ℝ)^4621 ≤ (8833443870543/20000000000000 : ℝ)^3597 := by
    have hnat : (5293523443 : ℕ)^4621*20000000000000^3597 ≤ 8833443870543^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293523443 10000000000 8833443870543 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847345229/5000000000 : ℝ)^4621 ≤ (5112067087137/50000000000000 : ℝ)^3597 := by
    have hnat : (847345229 : ℕ)^4621*50000000000000^3597 ≤ 5112067087137^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847345229 5000000000 5112067087137 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427518649/10000000000 : ℝ)^4621 ≤ (4560864645787/10000000000000 : ℝ)^3597 := by
    have hnat : (5427518649 : ℕ)^4621*10000000000000^3597 ≤ 4560864645787^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427518649 10000000000 4560864645787 10000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293523443/10000000000 : ℝ), (-847345229/5000000000 : ℝ), (5427518649/10000000000 : ℝ)] ![(8833443870543/20000000000000 : ℝ), (5112067087137/50000000000000 : ℝ), (4560864645787/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293523443/10000000000 : ℝ)|^4621 ≤ (8833443870543/20000000000000 : ℝ)^3597
        have hw : |(5293523443/10000000000 : ℝ)|=(5293523443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-847345229/5000000000 : ℝ)|^4621 ≤ (5112067087137/50000000000000 : ℝ)^3597
        have hw : |(-847345229/5000000000 : ℝ)|=(847345229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427518649/10000000000 : ℝ)|^4621 ≤ (4560864645787/10000000000000 : ℝ)^3597
        have hw : |(5427518649/10000000000 : ℝ)|=(5427518649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s3_6 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293523453/10000000000 : ℝ)*x 0 + (678439831/1250000000 : ℝ)*x 1 + (-338938089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293523453/10000000000 : ℝ)^4621 ≤ (690112804061/1562500000000 : ℝ)^3597 := by
    have hnat : (5293523453 : ℕ)^4621*1562500000000^3597 ≤ 690112804061^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293523453 10000000000 690112804061 1562500000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678439831/1250000000 : ℝ)^4621 ≤ (22804323223537/50000000000000 : ℝ)^3597 := by
    have hnat : (678439831 : ℕ)^4621*50000000000000^3597 ≤ 22804323223537^3597*1250000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678439831 1250000000 22804323223537 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338938089/2000000000 : ℝ)^4621 ≤ (10224134073517/100000000000000 : ℝ)^3597 := by
    have hnat : (338938089 : ℕ)^4621*100000000000000^3597 ≤ 10224134073517^3597*2000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338938089 2000000000 10224134073517 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293523453/10000000000 : ℝ), (678439831/1250000000 : ℝ), (-338938089/2000000000 : ℝ)] ![(690112804061/1562500000000 : ℝ), (22804323223537/50000000000000 : ℝ), (10224134073517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293523453/10000000000 : ℝ)|^4621 ≤ (690112804061/1562500000000 : ℝ)^3597
        have hw : |(5293523453/10000000000 : ℝ)|=(5293523453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678439831/1250000000 : ℝ)|^4621 ≤ (22804323223537/50000000000000 : ℝ)^3597
        have hw : |(678439831/1250000000 : ℝ)|=(678439831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-338938089/2000000000 : ℝ)|^4621 ≤ (10224134073517/100000000000000 : ℝ)^3597
        have hw : |(-338938089/2000000000 : ℝ)|=(338938089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s3_7 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849387187/2000000000 : ℝ)*x 0 + (2248610933/5000000000 : ℝ)*x 1 + (2004127159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849387187/2000000000 : ℝ)^4621 ≤ (6656189441419/20000000000000 : ℝ)^3597 := by
    have hnat : (849387187 : ℕ)^4621*20000000000000^3597 ≤ 6656189441419^3597*2000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849387187 2000000000 6656189441419 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248610933/5000000000 : ℝ)^4621 ≤ (4477689050057/12500000000000 : ℝ)^3597 := by
    have hnat : (2248610933 : ℕ)^4621*12500000000000^3597 ≤ 4477689050057^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248610933 5000000000 4477689050057 12500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004127159/5000000000 : ℝ)^4621 ≤ (30897540373279/100000000000000 : ℝ)^3597 := by
    have hnat : (2004127159 : ℕ)^4621*100000000000000^3597 ≤ 30897540373279^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004127159 5000000000 30897540373279 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849387187/2000000000 : ℝ), (2248610933/5000000000 : ℝ), (2004127159/5000000000 : ℝ)] ![(6656189441419/20000000000000 : ℝ), (4477689050057/12500000000000 : ℝ), (30897540373279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849387187/2000000000 : ℝ)|^4621 ≤ (6656189441419/20000000000000 : ℝ)^3597
        have hw : |(849387187/2000000000 : ℝ)|=(849387187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248610933/5000000000 : ℝ)|^4621 ≤ (4477689050057/12500000000000 : ℝ)^3597
        have hw : |(2248610933/5000000000 : ℝ)|=(2248610933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2004127159/5000000000 : ℝ)|^4621 ≤ (30897540373279/100000000000000 : ℝ)^3597
        have hw : |(2004127159/5000000000 : ℝ)|=(2004127159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1562_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (553/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15523/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15833/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5387/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15833/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5387/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15833/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5387/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15833/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5387/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15833/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5387/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15833/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5387/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5387/50000 : ℝ) ^ (4619/1024 : ℝ) ≤ (539774042200629/12500000000000000000 : ℝ) := by
    have hpowers : (5387/50000 : ℝ)^4619 ≤ (539774042200629/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5387 : ℕ)^4619*12500000000000000000^1024 ≤ 539774042200629^1024*50000^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5387 50000 539774042200629 12500000000000000000 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5387/50000 : ℝ)) (X := (539774042200629/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15833/100000 : ℝ) ^ (4619/1024 : ℝ) ≤ (6128808047165289/25000000000000000000 : ℝ) := by
    have hpowers : (15833/100000 : ℝ)^4619 ≤ (6128808047165289/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15833 : ℕ)^4619*25000000000000000000^1024 ≤ 6128808047165289^1024*100000^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15833 100000 6128808047165289 25000000000000000000 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15833/100000 : ℝ)) (X := (6128808047165289/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250539774042200629/6250000000000000000 : ℝ) ≤ (10000191456174453/10000000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (6250539774042200629/6250000000000000000 : ℝ)^1024 ≤ (10000191456174453/10000000000000000 : ℝ)^4619 := by
      have hnat : (6250539774042200629 : ℕ)^1024*10000000000000000^4619 ≤ 10000191456174453^4619*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250539774042200629 6250000000000000000 10000191456174453 10000000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000191456174453/10000000000000000 : ℝ)) (X := (6250539774042200629/6250000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007208356131566547/25000000000000000000 : ℝ) ≤ (10000639145147061/10000000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (25007208356131566547/25000000000000000000 : ℝ)^1024 ≤ (10000639145147061/10000000000000000 : ℝ)^4619 := by
      have hnat : (25007208356131566547 : ℕ)^1024*10000000000000000^4619 ≤ 10000639145147061^4619*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007208356131566547 25000000000000000000 10000639145147061 10000000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000639145147061/10000000000000000 : ℝ)) (X := (25007208356131566547/25000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506128808047165289/12500000000000000000 : ℝ) ≤ (10001086834119669/10000000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (12506128808047165289/12500000000000000000 : ℝ)^1024 ≤ (10001086834119669/10000000000000000 : ℝ)^4619 := by
      have hnat : (12506128808047165289 : ℕ)^1024*10000000000000000^4619 ≤ 10001086834119669^4619*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506128808047165289 12500000000000000000 10001086834119669 10000000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001086834119669/10000000000000000 : ℝ)) (X := (12506128808047165289/12500000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(539774042200629/12500000000000000000 : ℝ) ≤ ((50581321774804800543/50590000000000000000 : ℝ)+2*(6995140197/7904687500000 : ℝ)*(5387/50000 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (50581321774804800543/50590000000000000000 : ℝ)+2*(6995140197/7904687500000 : ℝ)*(5387/50000 : ℝ)=(10000191456174453/10000000000000000 : ℝ) by norm_num, show 1+2*(539774042200629/12500000000000000000 : ℝ)=(6250539774042200629/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6128808047165289/25000000000000000000 : ℝ)+(539774042200629/12500000000000000000 : ℝ) ≤ ((50581321774804800543/50590000000000000000 : ℝ)+(6995140197/7904687500000 : ℝ)*((15833/100000 : ℝ)+(5387/50000 : ℝ)))^(4619/1024 : ℝ) := by
    rw [show (50581321774804800543/50590000000000000000 : ℝ)+(6995140197/7904687500000 : ℝ)*((15833/100000 : ℝ)+(5387/50000 : ℝ))=(10000639145147061/10000000000000000 : ℝ) by norm_num, show 1+(6128808047165289/25000000000000000000 : ℝ)+(539774042200629/12500000000000000000 : ℝ)=(25007208356131566547/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6128808047165289/25000000000000000000 : ℝ) ≤ ((50581321774804800543/50590000000000000000 : ℝ)+2*(6995140197/7904687500000 : ℝ)*(15833/100000 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (50581321774804800543/50590000000000000000 : ℝ)+2*(6995140197/7904687500000 : ℝ)*(15833/100000 : ℝ)=(10001086834119669/10000000000000000 : ℝ) by norm_num, show 1+2*(6128808047165289/25000000000000000000 : ℝ)=(12506128808047165289/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (50581321774804800543/50590000000000000000 : ℝ)*(X 1 0+X 2 0)+(6995140197/7904687500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (5387/50000 : ℝ)) (hi := (15833/100000 : ℝ)) (c := (50581321774804800543/50590000000000000000 : ℝ)) (alpha := (6995140197/7904687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (50581321774804800543/50590000000000000000 : ℝ)*(X 0 1+X 2 1)+(6995140197/7904687500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (5387/50000 : ℝ)) (hi := (15833/100000 : ℝ)) (c := (50581321774804800543/50590000000000000000 : ℝ)) (alpha := (6995140197/7904687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (50581321774804800543/50590000000000000000 : ℝ)*(X 0 2+X 1 2)+(6995140197/7904687500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (5387/50000 : ℝ)) (hi := (15833/100000 : ℝ)) (c := (50581321774804800543/50590000000000000000 : ℝ)) (alpha := (6995140197/7904687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-71853119/400000000 : ℝ)*X 0 0+(1357160031/2500000000 : ℝ)*X 0 1+(652266349/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349164431/10000000000 : ℝ)*X 1 0+(-1904078119/10000000000 : ℝ)*X 1 1+(5218130873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334322759/625000000 : ℝ)*X 2 0+(208725241/400000000 : ℝ)*X 2 1+(-1904078303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4246869347/10000000000 : ℝ)*X 0 0+(2002810797/5000000000 : ℝ)*X 0 1+(562479347/1250000000 : ℝ)*X 0 2+(4246869347/10000000000 : ℝ)*X 1 0+(2002810797/5000000000 : ℝ)*X 1 1+(562479347/1250000000 : ℝ)*X 1 2+(4246869347/10000000000 : ℝ)*X 2 0+(2002810797/5000000000 : ℝ)*X 2 1+(562479347/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1796356467/10000000000 : ℝ)*X 0 0+(5219243799/10000000000 : ℝ)*X 0 1+(1356879679/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293523443/10000000000 : ℝ)*X 1 0+(-847345229/5000000000 : ℝ)*X 1 1+(5427518649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293523453/10000000000 : ℝ)*X 2 0+(678439831/1250000000 : ℝ)*X 2 1+(-338938089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((849387187/2000000000 : ℝ)*X 0 0+(2248610933/5000000000 : ℝ)*X 0 1+(2004127159/5000000000 : ℝ)*X 0 2+(849387187/2000000000 : ℝ)*X 1 0+(2248610933/5000000000 : ℝ)*X 1 1+(2004127159/5000000000 : ℝ)*X 1 2+(849387187/2000000000 : ℝ)*X 2 0+(2248610933/5000000000 : ℝ)*X 2 1+(2004127159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2464689902894740845804885429/632375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103268461/12500000000000 : ℝ)*(base19) + (12143489/2000000000000 : ℝ)*(base23) + (35425157/100000000000000 : ℝ)*(lower2) + (97232147/50000000000000 : ℝ)*(upper3) + (437037/800000000000 : ℝ)*(lower4) + (846730562797799/25000000000000 : ℝ)*(major0) + (846730562797799/25000000000000 : ℝ)*(major1) + (846730562797799/25000000000000 : ℝ)*(major2) + (4750402217643131/100000000000000 : ℝ)*(sp0) + (4750412808919373/100000000000000 : ℝ)*(sp1) + (4750413027892611/100000000000000 : ℝ)*(sp2) + (1011711912106253/50000000000000 : ℝ)*(sp3) + (1141742393/10000000000000 : ℝ)*(sp4) + (432074107/6250000000000 : ℝ)*(sp7) + (2023430737398219/100000000000000 : ℝ)*(f.failure) + (4750413635067061/100000000000000 : ℝ)*(f.sum) + (287594266650403/25295000000000000000000000000 : ℝ)*base65 + (2851129267468895143/1264750000000000000000000000000000 : ℝ)*base68 + (6058466002170395143/1264750000000000000000000000000000 : ℝ)*base70 + (3177042846004854857/1264750000000000000000000000000000 : ℝ)*base71 + (39949526072313/25295000000000000000000000000 : ℝ)*base73 + (1657218526373854857/1264750000000000000000000000000000 : ℝ)*base75 + (6913976625995104857/1264750000000000000000000000000000 : ℝ)*base77 + (3521872676356354857/1264750000000000000000000000000000 : ℝ)*base79 + (128113726572163/25295000000000000000000000000 : ℝ)*base81 + (49338173/5000000000000000000000 : ℝ)*base89 + (49338173/5000000000000000000000 : ℝ)*base91 + (49338173/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143778482905590324405686151/25295000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130714423/12500000000000 : ℝ)*(base19) + (1144041149/100000000000000 : ℝ)*(base23) + (62136997/50000000000000 : ℝ)*(upper3) + (9884839/25000000000000 : ℝ)*(lower4) + (65169567/50000000000000 : ℝ)*(upper5) + (68464712766181/2000000000000 : ℝ)*(major0) + (68464712766181/2000000000000 : ℝ)*(major1) + (68464712766181/2000000000000 : ℝ)*(major2) + (15364239737/100000000000000 : ℝ)*(sp1) + (16749687987/100000000000000 : ℝ)*(sp2) + (4801345838267133/100000000000000 : ℝ)*(sp4) + (1200332357078003/25000000000000 : ℝ)*(sp5) + (1200331986134499/25000000000000 : ℝ)*(sp6) + (15977541006891/781250000000 : ℝ)*(sp7) + (15977541006891/781250000000 : ℝ)*(f.failure) + (4801345838267133/100000000000000 : ℝ)*(f.sum) + (3950881394891/5059000000000000000000000000 : ℝ)*base66 + (445660945600336283/101180000000000000000000000000000 : ℝ)*base67 + (62186250805076283/101180000000000000000000000000000 : ℝ)*base69 + (338409890269103717/101180000000000000000000000000000 : ℝ)*base72 + (44333380198709/5059000000000000000000000000 : ℝ)*base73 + (854562146571096283/101180000000000000000000000000000 : ℝ)*base75 + (231651752134356283/101180000000000000000000000000000 : ℝ)*base77 + (1836553284377456283/101180000000000000000000000000000 : ℝ)*base79 + (16527479035483/5059000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (177053/39062500000000000000 : ℝ)*base90 + (177053/39062500000000000000 : ℝ)*base92 + (177053/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1562_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15523/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1562_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1562_s4_0 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1122859/6250000 : ℝ)*x 0 + (5426989223/10000000000 : ℝ)*x 1 + (5219618347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1122859/6250000 : ℝ)^4621 ≤ (137755652939/1250000000000 : ℝ)^3597 := by
    have hnat : (1122859 : ℕ)^4621*1250000000000^3597 ≤ 137755652939^3597*6250000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122859 6250000 137755652939 1250000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426989223/10000000000 : ℝ)^4621 ≤ (356272899507/781250000000 : ℝ)^3597 := by
    have hnat : (5426989223 : ℕ)^4621*781250000000^3597 ≤ 356272899507^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426989223 10000000000 356272899507 781250000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219618347/10000000000 : ℝ)^4621 ≤ (43376616615021/100000000000000 : ℝ)^3597 := by
    have hnat : (5219618347 : ℕ)^4621*100000000000000^3597 ≤ 43376616615021^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219618347 10000000000 43376616615021 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1122859/6250000 : ℝ), (5426989223/10000000000 : ℝ), (5219618347/10000000000 : ℝ)] ![(137755652939/1250000000000 : ℝ), (356272899507/781250000000 : ℝ), (43376616615021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1122859/6250000 : ℝ)|^4621 ≤ (137755652939/1250000000000 : ℝ)^3597
        have hw : |(-1122859/6250000 : ℝ)|=(1122859/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426989223/10000000000 : ℝ)|^4621 ≤ (356272899507/781250000000 : ℝ)^3597
        have hw : |(5426989223/10000000000 : ℝ)|=(5426989223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219618347/10000000000 : ℝ)|^4621 ≤ (43376616615021/100000000000000 : ℝ)^3597
        have hw : |(5219618347/10000000000 : ℝ)|=(5219618347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s4_1 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348728077/10000000000 : ℝ)*x 0 + (-380536301/2000000000 : ℝ)*x 1 + (65245229/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348728077/10000000000 : ℝ)^4621 ≤ (1790393169533/4000000000000 : ℝ)^3597 := by
    have hnat : (5348728077 : ℕ)^4621*4000000000000^3597 ≤ 1790393169533^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348728077 10000000000 1790393169533 4000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (380536301/2000000000 : ℝ)^4621 ≤ (5931777212533/50000000000000 : ℝ)^3597 := by
    have hnat : (380536301 : ℕ)^4621*50000000000000^3597 ≤ 5931777212533^3597*2000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380536301 2000000000 5931777212533 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65245229/125000000 : ℝ)^4621 ≤ (21688308163383/50000000000000 : ℝ)^3597 := by
    have hnat : (65245229 : ℕ)^4621*50000000000000^3597 ≤ 21688308163383^3597*125000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65245229 125000000 21688308163383 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348728077/10000000000 : ℝ), (-380536301/2000000000 : ℝ), (65245229/125000000 : ℝ)] ![(1790393169533/4000000000000 : ℝ), (5931777212533/50000000000000 : ℝ), (21688308163383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348728077/10000000000 : ℝ)|^4621 ≤ (1790393169533/4000000000000 : ℝ)^3597
        have hw : |(5348728077/10000000000 : ℝ)|=(5348728077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-380536301/2000000000 : ℝ)|^4621 ≤ (5931777212533/50000000000000 : ℝ)^3597
        have hw : |(-380536301/2000000000 : ℝ)|=(380536301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65245229/125000000 : ℝ)|^4621 ≤ (21688308163383/50000000000000 : ℝ)^3597
        have hw : |(65245229/125000000 : ℝ)|=(65245229/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s4_2 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534872801/1000000000 : ℝ)*x 0 + (5219618727/10000000000 : ℝ)*x 1 + (-1902681053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534872801/1000000000 : ℝ)^4621 ≤ (22379914259017/50000000000000 : ℝ)^3597 := by
    have hnat : (534872801 : ℕ)^4621*50000000000000^3597 ≤ 22379914259017^3597*1000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534872801 1000000000 22379914259017 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219618727/10000000000 : ℝ)^4621 ≤ (43376620671937/100000000000000 : ℝ)^3597 := by
    have hnat : (5219618727 : ℕ)^4621*100000000000000^3597 ≤ 43376620671937^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219618727 10000000000 43376620671937 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1902681053/10000000000 : ℝ)^4621 ≤ (370735962639/3125000000000 : ℝ)^3597 := by
    have hnat : (1902681053 : ℕ)^4621*3125000000000^3597 ≤ 370735962639^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902681053 10000000000 370735962639 3125000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534872801/1000000000 : ℝ), (5219618727/10000000000 : ℝ), (-1902681053/10000000000 : ℝ)] ![(22379914259017/50000000000000 : ℝ), (43376620671937/100000000000000 : ℝ), (370735962639/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534872801/1000000000 : ℝ)|^4621 ≤ (22379914259017/50000000000000 : ℝ)^3597
        have hw : |(534872801/1000000000 : ℝ)|=(534872801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219618727/10000000000 : ℝ)|^4621 ≤ (43376620671937/100000000000000 : ℝ)^3597
        have hw : |(5219618727/10000000000 : ℝ)|=(5219618727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1902681053/10000000000 : ℝ)|^4621 ≤ (370735962639/3125000000000 : ℝ)^3597
        have hw : |(-1902681053/10000000000 : ℝ)|=(1902681053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s4_3 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4247024991/10000000000 : ℝ)*x 0 + (4009289179/10000000000 : ℝ)*x 1 + (1124033169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247024991/10000000000 : ℝ)^4621 ≤ (33281843768377/100000000000000 : ℝ)^3597 := by
    have hnat : (4247024991 : ℕ)^4621*100000000000000^3597 ≤ 33281843768377^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247024991 10000000000 33281843768377 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4009289179/10000000000 : ℝ)^4621 ≤ (3863473614599/12500000000000 : ℝ)^3597 := by
    have hnat : (4009289179 : ℕ)^4621*12500000000000^3597 ≤ 3863473614599^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009289179 10000000000 3863473614599 12500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124033169/2500000000 : ℝ)^4621 ≤ (8952591826153/25000000000000 : ℝ)^3597 := by
    have hnat : (1124033169 : ℕ)^4621*25000000000000^3597 ≤ 8952591826153^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124033169 2500000000 8952591826153 25000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247024991/10000000000 : ℝ), (4009289179/10000000000 : ℝ), (1124033169/2500000000 : ℝ)] ![(33281843768377/100000000000000 : ℝ), (3863473614599/12500000000000 : ℝ), (8952591826153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247024991/10000000000 : ℝ)|^4621 ≤ (33281843768377/100000000000000 : ℝ)^3597
        have hw : |(4247024991/10000000000 : ℝ)|=(4247024991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4009289179/10000000000 : ℝ)|^4621 ≤ (3863473614599/12500000000000 : ℝ)^3597
        have hw : |(4009289179/10000000000 : ℝ)|=(4009289179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124033169/2500000000 : ℝ)|^4621 ≤ (8952591826153/25000000000000 : ℝ)^3597
        have hw : |(1124033169/2500000000 : ℝ)|=(1124033169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s4_4 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-898300823/5000000000 : ℝ)*x 0 + (1044139743/2000000000 : ℝ)*x 1 + (5425900819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898300823/5000000000 : ℝ)^4621 ≤ (11020666945693/100000000000000 : ℝ)^3597 := by
    have hnat : (898300823 : ℕ)^4621*100000000000000^3597 ≤ 11020666945693^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898300823 5000000000 11020666945693 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044139743/2000000000 : ℝ)^4621 ≤ (8677630213383/20000000000000 : ℝ)^3597 := by
    have hnat : (1044139743 : ℕ)^4621*20000000000000^3597 ≤ 8677630213383^3597*2000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044139743 2000000000 8677630213383 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425900819/10000000000 : ℝ)^4621 ≤ (45591181970349/100000000000000 : ℝ)^3597 := by
    have hnat : (5425900819 : ℕ)^4621*100000000000000^3597 ≤ 45591181970349^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425900819 10000000000 45591181970349 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-898300823/5000000000 : ℝ), (1044139743/2000000000 : ℝ), (5425900819/10000000000 : ℝ)] ![(11020666945693/100000000000000 : ℝ), (8677630213383/20000000000000 : ℝ), (45591181970349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-898300823/5000000000 : ℝ)|^4621 ≤ (11020666945693/100000000000000 : ℝ)^3597
        have hw : |(-898300823/5000000000 : ℝ)|=(898300823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044139743/2000000000 : ℝ)|^4621 ≤ (8677630213383/20000000000000 : ℝ)^3597
        have hw : |(1044139743/2000000000 : ℝ)|=(1044139743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425900819/10000000000 : ℝ)|^4621 ≤ (45591181970349/100000000000000 : ℝ)^3597
        have hw : |(5425900819/10000000000 : ℝ)|=(5425900819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s4_5 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293916811/10000000000 : ℝ)*x 0 + (-848199737/5000000000 : ℝ)*x 1 + (1356475211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293916811/10000000000 : ℝ)^4621 ≤ (2760714742169/6250000000000 : ℝ)^3597 := by
    have hnat : (5293916811 : ℕ)^4621*6250000000000^3597 ≤ 2760714742169^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293916811 10000000000 2760714742169 6250000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848199737/5000000000 : ℝ)^4621 ≤ (10237381863647/100000000000000 : ℝ)^3597 := by
    have hnat : (848199737 : ℕ)^4621*100000000000000^3597 ≤ 10237381863647^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848199737 5000000000 10237381863647 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356475211/2500000000 : ℝ)^4621 ≤ (45591182240213/100000000000000 : ℝ)^3597 := by
    have hnat : (1356475211 : ℕ)^4621*100000000000000^3597 ≤ 45591182240213^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356475211 2500000000 45591182240213 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293916811/10000000000 : ℝ), (-848199737/5000000000 : ℝ), (1356475211/2500000000 : ℝ)] ![(2760714742169/6250000000000 : ℝ), (10237381863647/100000000000000 : ℝ), (45591182240213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293916811/10000000000 : ℝ)|^4621 ≤ (2760714742169/6250000000000 : ℝ)^3597
        have hw : |(5293916811/10000000000 : ℝ)|=(5293916811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-848199737/5000000000 : ℝ)|^4621 ≤ (10237381863647/100000000000000 : ℝ)^3597
        have hw : |(-848199737/5000000000 : ℝ)|=(848199737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356475211/2500000000 : ℝ)|^4621 ≤ (45591182240213/100000000000000 : ℝ)^3597
        have hw : |(1356475211/2500000000 : ℝ)|=(1356475211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s4_6 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105878333/200000000 : ℝ)*x 0 + (2712950479/5000000000 : ℝ)*x 1 + (-1696399539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105878333/200000000 : ℝ)^4621 ≤ (22085717074461/50000000000000 : ℝ)^3597 := by
    have hnat : (105878333 : ℕ)^4621*50000000000000^3597 ≤ 22085717074461^3597*200000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105878333 200000000 22085717074461 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712950479/5000000000 : ℝ)^4621 ≤ (45591183470791/100000000000000 : ℝ)^3597 := by
    have hnat : (2712950479 : ℕ)^4621*100000000000000^3597 ≤ 45591183470791^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712950479 5000000000 45591183470791 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1696399539/10000000000 : ℝ)^4621 ≤ (1279672795947/12500000000000 : ℝ)^3597 := by
    have hnat : (1696399539 : ℕ)^4621*12500000000000^3597 ≤ 1279672795947^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696399539 10000000000 1279672795947 12500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105878333/200000000 : ℝ), (2712950479/5000000000 : ℝ), (-1696399539/10000000000 : ℝ)] ![(22085717074461/50000000000000 : ℝ), (45591183470791/100000000000000 : ℝ), (1279672795947/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105878333/200000000 : ℝ)|^4621 ≤ (22085717074461/50000000000000 : ℝ)^3597
        have hw : |(105878333/200000000 : ℝ)|=(105878333/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712950479/5000000000 : ℝ)|^4621 ≤ (45591183470791/100000000000000 : ℝ)^3597
        have hw : |(2712950479/5000000000 : ℝ)|=(2712950479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1696399539/10000000000 : ℝ)|^4621 ≤ (1279672795947/12500000000000 : ℝ)^3597
        have hw : |(-1696399539/10000000000 : ℝ)|=(1696399539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s4_7 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2123544407/5000000000 : ℝ)*x 0 + (4493596991/10000000000 : ℝ)*x 1 + (1002960909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123544407/5000000000 : ℝ)^4621 ≤ (33282486302557/100000000000000 : ℝ)^3597 := by
    have hnat : (2123544407 : ℕ)^4621*100000000000000^3597 ≤ 33282486302557^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123544407 5000000000 33282486302557 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493596991/10000000000 : ℝ)^4621 ≤ (17892211990291/50000000000000 : ℝ)^3597 := by
    have hnat : (4493596991 : ℕ)^4621*50000000000000^3597 ≤ 17892211990291^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493596991 10000000000 17892211990291 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002960909/2500000000 : ℝ)^4621 ≤ (30933089705597/100000000000000 : ℝ)^3597 := by
    have hnat : (1002960909 : ℕ)^4621*100000000000000^3597 ≤ 30933089705597^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002960909 2500000000 30933089705597 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123544407/5000000000 : ℝ), (4493596991/10000000000 : ℝ), (1002960909/2500000000 : ℝ)] ![(33282486302557/100000000000000 : ℝ), (17892211990291/50000000000000 : ℝ), (30933089705597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123544407/5000000000 : ℝ)|^4621 ≤ (33282486302557/100000000000000 : ℝ)^3597
        have hw : |(2123544407/5000000000 : ℝ)|=(2123544407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493596991/10000000000 : ℝ)|^4621 ≤ (17892211990291/50000000000000 : ℝ)^3597
        have hw : |(4493596991/10000000000 : ℝ)|=(4493596991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002960909/2500000000 : ℝ)|^4621 ≤ (30933089705597/100000000000000 : ℝ)^3597
        have hw : |(1002960909/2500000000 : ℝ)|=(1002960909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1562_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15523/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (2773/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15523/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (553/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15523/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (553/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15523/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (553/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15523/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (553/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15523/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (553/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15523/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (553/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (553/5000 : ℝ) ^ (4619/1024 : ℝ) ≤ (2429942035668963/50000000000000000000 : ℝ) := by
    have hpowers : (553/5000 : ℝ)^4619 ≤ (2429942035668963/50000000000000000000 : ℝ)^1024 := by
      have hnat : (553 : ℕ)^4619*50000000000000000000^1024 ≤ 2429942035668963^1024*5000^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        553 5000 2429942035668963 50000000000000000000 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (553/5000 : ℝ)) (X := (2429942035668963/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15523/100000 : ℝ) ^ (4619/1024 : ℝ) ≤ (2802914049854761/12500000000000000000 : ℝ) := by
    have hpowers : (15523/100000 : ℝ)^4619 ≤ (2802914049854761/12500000000000000000 : ℝ)^1024 := by
      have hnat : (15523 : ℕ)^4619*12500000000000000000^1024 ≤ 2802914049854761^1024*100000^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15523 100000 2802914049854761 12500000000000000000 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15523/100000 : ℝ)) (X := (2802914049854761/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002429942035668963/25000000000000000000 : ℝ) ≤ (1000021547231279/1000000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (25002429942035668963/25000000000000000000 : ℝ)^1024 ≤ (1000021547231279/1000000000000000 : ℝ)^4619 := by
      have hnat : (25002429942035668963 : ℕ)^1024*1000000000000000^4619 ≤ 1000021547231279^4619*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002429942035668963 25000000000000000000 1000021547231279 1000000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000021547231279/1000000000000000 : ℝ)) (X := (25002429942035668963/25000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013641598235088007/50000000000000000000 : ℝ) ≤ (10000604785178399/10000000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (50013641598235088007/50000000000000000000 : ℝ)^1024 ≤ (10000604785178399/10000000000000000 : ℝ)^4619 := by
      have hnat : (50013641598235088007 : ℕ)^1024*10000000000000000^4619 ≤ 10000604785178399^4619*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013641598235088007 50000000000000000000 10000604785178399 10000000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000604785178399/10000000000000000 : ℝ)) (X := (50013641598235088007/50000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252802914049854761/6250000000000000000 : ℝ) ≤ (1250124262255501/1250000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (6252802914049854761/6250000000000000000 : ℝ)^1024 ≤ (1250124262255501/1250000000000000 : ℝ)^4619 := by
      have hnat : (6252802914049854761 : ℕ)^1024*1250000000000000^4619 ≤ 1250124262255501^4619*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252802914049854761 6250000000000000000 1250124262255501 1250000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250124262255501/1250000000000000 : ℝ)) (X := (6252802914049854761/6250000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2429942035668963/50000000000000000000 : ℝ) ≤ ((4462235005234471069/4463000000000000000 : ℝ)+2*(389312865609/446300000000000 : ℝ)*(553/5000 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (4462235005234471069/4463000000000000000 : ℝ)+2*(389312865609/446300000000000 : ℝ)*(553/5000 : ℝ)=(1000021547231279/1000000000000000 : ℝ) by norm_num, show 1+2*(2429942035668963/50000000000000000000 : ℝ)=(25002429942035668963/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2802914049854761/12500000000000000000 : ℝ)+(2429942035668963/50000000000000000000 : ℝ) ≤ ((4462235005234471069/4463000000000000000 : ℝ)+(389312865609/446300000000000 : ℝ)*((15523/100000 : ℝ)+(553/5000 : ℝ)))^(4619/1024 : ℝ) := by
    rw [show (4462235005234471069/4463000000000000000 : ℝ)+(389312865609/446300000000000 : ℝ)*((15523/100000 : ℝ)+(553/5000 : ℝ))=(10000604785178399/10000000000000000 : ℝ) by norm_num, show 1+(2802914049854761/12500000000000000000 : ℝ)+(2429942035668963/50000000000000000000 : ℝ)=(50013641598235088007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2802914049854761/12500000000000000000 : ℝ) ≤ ((4462235005234471069/4463000000000000000 : ℝ)+2*(389312865609/446300000000000 : ℝ)*(15523/100000 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (4462235005234471069/4463000000000000000 : ℝ)+2*(389312865609/446300000000000 : ℝ)*(15523/100000 : ℝ)=(1250124262255501/1250000000000000 : ℝ) by norm_num, show 1+2*(2802914049854761/12500000000000000000 : ℝ)=(6252802914049854761/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4462235005234471069/4463000000000000000 : ℝ)*(X 1 0+X 2 0)+(389312865609/446300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (15523/100000 : ℝ)) (c := (4462235005234471069/4463000000000000000 : ℝ)) (alpha := (389312865609/446300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4462235005234471069/4463000000000000000 : ℝ)*(X 0 1+X 2 1)+(389312865609/446300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (15523/100000 : ℝ)) (c := (4462235005234471069/4463000000000000000 : ℝ)) (alpha := (389312865609/446300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4462235005234471069/4463000000000000000 : ℝ)*(X 0 2+X 1 2)+(389312865609/446300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (15523/100000 : ℝ)) (c := (4462235005234471069/4463000000000000000 : ℝ)) (alpha := (389312865609/446300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1122859/6250000 : ℝ)*X 0 0+(5426989223/10000000000 : ℝ)*X 0 1+(5219618347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348728077/10000000000 : ℝ)*X 1 0+(-380536301/2000000000 : ℝ)*X 1 1+(65245229/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534872801/1000000000 : ℝ)*X 2 0+(5219618727/10000000000 : ℝ)*X 2 1+(-1902681053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4247024991/10000000000 : ℝ)*X 0 0+(4009289179/10000000000 : ℝ)*X 0 1+(1124033169/2500000000 : ℝ)*X 0 2+(4247024991/10000000000 : ℝ)*X 1 0+(4009289179/10000000000 : ℝ)*X 1 1+(1124033169/2500000000 : ℝ)*X 1 2+(4247024991/10000000000 : ℝ)*X 2 0+(4009289179/10000000000 : ℝ)*X 2 1+(1124033169/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-898300823/5000000000 : ℝ)*X 0 0+(1044139743/2000000000 : ℝ)*X 0 1+(5425900819/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293916811/10000000000 : ℝ)*X 1 0+(-848199737/5000000000 : ℝ)*X 1 1+(1356475211/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((105878333/200000000 : ℝ)*X 2 0+(2712950479/5000000000 : ℝ)*X 2 1+(-1696399539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2123544407/5000000000 : ℝ)*X 0 0+(4493596991/10000000000 : ℝ)*X 0 1+(1002960909/2500000000 : ℝ)*X 0 2+(2123544407/5000000000 : ℝ)*X 1 0+(4493596991/10000000000 : ℝ)*X 1 1+(1002960909/2500000000 : ℝ)*X 1 2+(2123544407/5000000000 : ℝ)*X 2 0+(4493596991/10000000000 : ℝ)*X 2 1+(1002960909/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (363845109631472286579288939/223150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (397089023/50000000000000 : ℝ)*(base19) + (78739397/10000000000000 : ℝ)*(base23) + (18691889/100000000000000 : ℝ)*(lower2) + (8167269/12500000000000 : ℝ)*(upper5) + (3438195318156077/100000000000000 : ℝ)*(major0) + (3438195318156077/100000000000000 : ℝ)*(major1) + (3438195318156077/100000000000000 : ℝ)*(major2) + (482230163606753/10000000000000 : ℝ)*(sp0) + (96446372299089/2000000000000 : ℝ)*(sp1) + (4822327264644921/100000000000000 : ℝ)*(sp2) + (2054055596542661/100000000000000 : ℝ)*(sp3) + (13207985681/50000000000000 : ℝ)*(sp4) + (1728581279/20000000000000 : ℝ)*(sp5) + (6933380741/100000000000000 : ℝ)*(sp7) + (1027031264961701/50000000000000 : ℝ)*(f.failure) + (4822328052038891/100000000000000 : ℝ)*(f.sum) + (26723598881199/11157500000000000000000000000 : ℝ)*base65 + (1032355374179033687/446300000000000000000000000000000 : ℝ)*base68 + (1002488456008033687/446300000000000000000000000000000 : ℝ)*base70 + (345600783444033687/446300000000000000000000000000000 : ℝ)*base72 + (13295936217657/22315000000000000000000000000 : ℝ)*base74 + (2499313898662366313/446300000000000000000000000000000 : ℝ)*base75 + (1450612008798533687/446300000000000000000000000000000 : ℝ)*base78 + (674025123894866313/446300000000000000000000000000000 : ℝ)*base79 + (557432440323/5578750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (11623533/2500000000000000000000 : ℝ)*base90 + (11623533/2500000000000000000000 : ℝ)*base92 + (11623533/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2769189647550788010077669403/223150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1629106669/100000000000000 : ℝ)*(base19) + (785900309/50000000000000 : ℝ)*(base23) + (31720449/12500000000000 : ℝ)*(upper3) + (1344639/2500000000000 : ℝ)*(lower4) + (282920393/100000000000000 : ℝ)*(upper5) + (3474496852955229/100000000000000 : ℝ)*(major0) + (3474496852955229/100000000000000 : ℝ)*(major1) + (3474496852955229/100000000000000 : ℝ)*(major2) + (12206294793/50000000000000 : ℝ)*(sp1) + (23379237481/100000000000000 : ℝ)*(sp2) + (121831083292969/2500000000000 : ℝ)*(sp4) + (974643458004501/20000000000000 : ℝ)*(sp5) + (243660919034033/5000000000000 : ℝ)*(sp6) + (2075749960540241/100000000000000 : ℝ)*(sp7) + (2075749960540241/100000000000000 : ℝ)*(f.failure) + (121831083292969/2500000000000 : ℝ)*(f.sum) + (38879012730949/22315000000000000000000000000 : ℝ)*base66 + (790407211947920199/446300000000000000000000000000000 : ℝ)*base68 + (128206505996579801/446300000000000000000000000000000 : ℝ)*base69 + (1124236764553920199/446300000000000000000000000000000 : ℝ)*base72 + (3662773698799/5578750000000000000000000000 : ℝ)*base73 + (2470886391393420199/446300000000000000000000000000000 : ℝ)*base76 + (530521256111820199/446300000000000000000000000000000 : ℝ)*base78 + (7456955449499979801/446300000000000000000000000000000 : ℝ)*base79 + (6587328733771/5578750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (26088647/5000000000000000000000 : ℝ)*base89 + (26088647/5000000000000000000000 : ℝ)*base91 + (26088647/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1562_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15523/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1562_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1562_s5_0 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1796598977/10000000000 : ℝ)*x 0 + (2713409289/5000000000 : ℝ)*x 1 + (326235797/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1796598977/10000000000 : ℝ)^4621 ≤ (11020645912747/100000000000000 : ℝ)^3597 := by
    have hnat : (1796598977 : ℕ)^4621*100000000000000^3597 ≤ 11020645912747^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796598977 10000000000 11020645912747 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713409289/5000000000 : ℝ)^4621 ≤ (2280054450201/5000000000000 : ℝ)^3597 := by
    have hnat : (2713409289 : ℕ)^4621*5000000000000^3597 ≤ 2280054450201^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713409289 5000000000 2280054450201 5000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326235797/625000000 : ℝ)^4621 ≤ (43378265064509/100000000000000 : ℝ)^3597 := by
    have hnat : (326235797 : ℕ)^4621*100000000000000^3597 ≤ 43378265064509^3597*625000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326235797 625000000 43378265064509 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1796598977/10000000000 : ℝ), (2713409289/5000000000 : ℝ), (326235797/625000000 : ℝ)] ![(11020645912747/100000000000000 : ℝ), (2280054450201/5000000000000 : ℝ), (43378265064509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1796598977/10000000000 : ℝ)|^4621 ≤ (11020645912747/100000000000000 : ℝ)^3597
        have hw : |(-1796598977/10000000000 : ℝ)|=(1796598977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713409289/5000000000 : ℝ)|^4621 ≤ (2280054450201/5000000000000 : ℝ)^3597
        have hw : |(2713409289/5000000000 : ℝ)|=(2713409289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326235797/625000000 : ℝ)|^4621 ≤ (43378265064509/100000000000000 : ℝ)^3597
        have hw : |(326235797/625000000 : ℝ)|=(326235797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s5_1 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348682957/10000000000 : ℝ)*x 0 + (-1902536247/10000000000 : ℝ)*x 1 + (5219772739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348682957/10000000000 : ℝ)^4621 ≤ (22379672085511/50000000000000 : ℝ)^3597 := by
    have hnat : (5348682957 : ℕ)^4621*50000000000000^3597 ≤ 22379672085511^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348682957 10000000000 22379672085511 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1902536247/10000000000 : ℝ)^4621 ≤ (185349857651/1562500000000 : ℝ)^3597 := by
    have hnat : (1902536247 : ℕ)^4621*1562500000000^3597 ≤ 185349857651^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902536247 10000000000 185349857651 1562500000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219772739/10000000000 : ℝ)^4621 ≤ (21689132462859/50000000000000 : ℝ)^3597 := by
    have hnat : (5219772739 : ℕ)^4621*50000000000000^3597 ≤ 21689132462859^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219772739 10000000000 21689132462859 50000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348682957/10000000000 : ℝ), (-1902536247/10000000000 : ℝ), (5219772739/10000000000 : ℝ)] ![(22379672085511/50000000000000 : ℝ), (185349857651/1562500000000 : ℝ), (21689132462859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348682957/10000000000 : ℝ)|^4621 ≤ (22379672085511/50000000000000 : ℝ)^3597
        have hw : |(5348682957/10000000000 : ℝ)|=(5348682957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1902536247/10000000000 : ℝ)|^4621 ≤ (185349857651/1562500000000 : ℝ)^3597
        have hw : |(-1902536247/10000000000 : ℝ)|=(1902536247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219772739/10000000000 : ℝ)|^4621 ≤ (21689132462859/50000000000000 : ℝ)^3597
        have hw : |(5219772739/10000000000 : ℝ)|=(5219772739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s5_2 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66858537/125000000 : ℝ)*x 0 + (2609886367/5000000000 : ℝ)*x 1 + (-1902536249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66858537/125000000 : ℝ)^4621 ≤ (44759344203273/100000000000000 : ℝ)^3597 := by
    have hnat : (66858537 : ℕ)^4621*100000000000000^3597 ≤ 44759344203273^3597*125000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66858537 125000000 44759344203273 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609886367/5000000000 : ℝ)^4621 ≤ (43378264872337/100000000000000 : ℝ)^3597 := by
    have hnat : (2609886367 : ℕ)^4621*100000000000000^3597 ≤ 43378264872337^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609886367 5000000000 43378264872337 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1902536249/10000000000 : ℝ)^4621 ≤ (2965597726421/25000000000000 : ℝ)^3597 := by
    have hnat : (1902536249 : ℕ)^4621*25000000000000^3597 ≤ 2965597726421^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902536249 10000000000 2965597726421 25000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66858537/125000000 : ℝ), (2609886367/5000000000 : ℝ), (-1902536249/10000000000 : ℝ)] ![(44759344203273/100000000000000 : ℝ), (43378264872337/100000000000000 : ℝ), (2965597726421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66858537/125000000 : ℝ)|^4621 ≤ (44759344203273/100000000000000 : ℝ)^3597
        have hw : |(66858537/125000000 : ℝ)|=(66858537/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609886367/5000000000 : ℝ)|^4621 ≤ (43378264872337/100000000000000 : ℝ)^3597
        have hw : |(2609886367/5000000000 : ℝ)|=(2609886367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1902536249/10000000000 : ℝ)|^4621 ≤ (2965597726421/25000000000000 : ℝ)^3597
        have hw : |(-1902536249/10000000000 : ℝ)|=(1902536249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s5_3 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2123520463/5000000000 : ℝ)*x 0 + (4009668149/10000000000 : ℝ)*x 1 + (2247875091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123520463/5000000000 : ℝ)^4621 ≤ (6656400838553/20000000000000 : ℝ)^3597 := by
    have hnat : (2123520463 : ℕ)^4621*20000000000000^3597 ≤ 6656400838553^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123520463 5000000000 6656400838553 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4009668149/10000000000 : ℝ)^4621 ≤ (6182308432093/20000000000000 : ℝ)^3597 := by
    have hnat : (4009668149 : ℕ)^4621*20000000000000^3597 ≤ 6182308432093^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009668149 10000000000 6182308432093 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247875091/5000000000 : ℝ)^4621 ≤ (7161290726287/20000000000000 : ℝ)^3597 := by
    have hnat : (2247875091 : ℕ)^4621*20000000000000^3597 ≤ 7161290726287^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247875091 5000000000 7161290726287 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123520463/5000000000 : ℝ), (4009668149/10000000000 : ℝ), (2247875091/5000000000 : ℝ)] ![(6656400838553/20000000000000 : ℝ), (6182308432093/20000000000000 : ℝ), (7161290726287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123520463/5000000000 : ℝ)|^4621 ≤ (6656400838553/20000000000000 : ℝ)^3597
        have hw : |(2123520463/5000000000 : ℝ)|=(2123520463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4009668149/10000000000 : ℝ)|^4621 ≤ (6182308432093/20000000000000 : ℝ)^3597
        have hw : |(4009668149/10000000000 : ℝ)|=(4009668149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247875091/5000000000 : ℝ)|^4621 ≤ (7161290726287/20000000000000 : ℝ)^3597
        have hw : |(2247875091/5000000000 : ℝ)|=(2247875091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s5_4 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-449156509/2500000000 : ℝ)*x 0 + (5220849527/10000000000 : ℝ)*x 1 + (2712866923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449156509/2500000000 : ℝ)^4621 ≤ (1377607393813/12500000000000 : ℝ)^3597 := by
    have hnat : (449156509 : ℕ)^4621*12500000000000^3597 ≤ 1377607393813^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449156509 2500000000 1377607393813 12500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220849527/10000000000 : ℝ)^4621 ≤ (43389761251737/100000000000000 : ℝ)^3597 := by
    have hnat : (5220849527 : ℕ)^4621*100000000000000^3597 ≤ 43389761251737^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220849527 10000000000 43389761251737 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712866923/5000000000 : ℝ)^4621 ≤ (11397344894973/25000000000000 : ℝ)^3597 := by
    have hnat : (2712866923 : ℕ)^4621*25000000000000^3597 ≤ 11397344894973^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712866923 5000000000 11397344894973 25000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-449156509/2500000000 : ℝ), (5220849527/10000000000 : ℝ), (2712866923/5000000000 : ℝ)] ![(1377607393813/12500000000000 : ℝ), (43389761251737/100000000000000 : ℝ), (11397344894973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-449156509/2500000000 : ℝ)|^4621 ≤ (1377607393813/12500000000000 : ℝ)^3597
        have hw : |(-449156509/2500000000 : ℝ)|=(449156509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220849527/10000000000 : ℝ)|^4621 ≤ (43389761251737/100000000000000 : ℝ)^3597
        have hw : |(5220849527/10000000000 : ℝ)|=(5220849527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712866923/5000000000 : ℝ)|^4621 ≤ (11397344894973/25000000000000 : ℝ)^3597
        have hw : |(2712866923/5000000000 : ℝ)|=(2712866923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s5_5 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293957919/10000000000 : ℝ)*x 0 + (-339315031/2000000000 : ℝ)*x 1 + (2712866923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293957919/10000000000 : ℝ)^4621 ≤ (4417187651759/10000000000000 : ℝ)^3597 := by
    have hnat : (5293957919 : ℕ)^4621*10000000000000^3597 ≤ 4417187651759^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293957919 10000000000 4417187651759 10000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339315031/2000000000 : ℝ)^4621 ≤ (10238743896243/100000000000000 : ℝ)^3597 := by
    have hnat : (339315031 : ℕ)^4621*100000000000000^3597 ≤ 10238743896243^3597*2000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339315031 2000000000 10238743896243 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712866923/5000000000 : ℝ)^4621 ≤ (11397344894973/25000000000000 : ℝ)^3597 := by
    have hnat : (2712866923 : ℕ)^4621*25000000000000^3597 ≤ 11397344894973^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712866923 5000000000 11397344894973 25000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293957919/10000000000 : ℝ), (-339315031/2000000000 : ℝ), (2712866923/5000000000 : ℝ)] ![(4417187651759/10000000000000 : ℝ), (10238743896243/100000000000000 : ℝ), (11397344894973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293957919/10000000000 : ℝ)|^4621 ≤ (4417187651759/10000000000000 : ℝ)^3597
        have hw : |(5293957919/10000000000 : ℝ)|=(5293957919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-339315031/2000000000 : ℝ)|^4621 ≤ (10238743896243/100000000000000 : ℝ)^3597
        have hw : |(-339315031/2000000000 : ℝ)|=(339315031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712866923/5000000000 : ℝ)|^4621 ≤ (11397344894973/25000000000000 : ℝ)^3597
        have hw : |(2712866923/5000000000 : ℝ)|=(2712866923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s5_6 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293957919/10000000000 : ℝ)*x 0 + (2712866923/5000000000 : ℝ)*x 1 + (-339315031/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293957919/10000000000 : ℝ)^4621 ≤ (4417187651759/10000000000000 : ℝ)^3597 := by
    have hnat : (5293957919 : ℕ)^4621*10000000000000^3597 ≤ 4417187651759^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293957919 10000000000 4417187651759 10000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712866923/5000000000 : ℝ)^4621 ≤ (11397344894973/25000000000000 : ℝ)^3597 := by
    have hnat : (2712866923 : ℕ)^4621*25000000000000^3597 ≤ 11397344894973^3597*5000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712866923 5000000000 11397344894973 25000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339315031/2000000000 : ℝ)^4621 ≤ (10238743896243/100000000000000 : ℝ)^3597 := by
    have hnat : (339315031 : ℕ)^4621*100000000000000^3597 ≤ 10238743896243^3597*2000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339315031 2000000000 10238743896243 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293957919/10000000000 : ℝ), (2712866923/5000000000 : ℝ), (-339315031/2000000000 : ℝ)] ![(4417187651759/10000000000000 : ℝ), (11397344894973/25000000000000 : ℝ), (10238743896243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293957919/10000000000 : ℝ)|^4621 ≤ (4417187651759/10000000000000 : ℝ)^3597
        have hw : |(5293957919/10000000000 : ℝ)|=(5293957919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712866923/5000000000 : ℝ)|^4621 ≤ (11397344894973/25000000000000 : ℝ)^3597
        have hw : |(2712866923/5000000000 : ℝ)|=(2712866923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-339315031/2000000000 : ℝ)|^4621 ≤ (10238743896243/100000000000000 : ℝ)^3597
        have hw : |(-339315031/2000000000 : ℝ)|=(339315031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1562_s5_7 (p : ℝ) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061776121/2500000000 : ℝ)*x 0 + (179728889/400000000 : ℝ)*x 1 + (4012214761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061776121/2500000000 : ℝ)^4621 ≤ (4160330507469/12500000000000 : ℝ)^3597 := by
    have hnat : (1061776121 : ℕ)^4621*12500000000000^3597 ≤ 4160330507469^3597*2500000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061776121 2500000000 4160330507469 12500000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179728889/400000000 : ℝ)^4621 ≤ (7156117999011/20000000000000 : ℝ)^3597 := by
    have hnat : (179728889 : ℕ)^4621*20000000000000^3597 ≤ 7156117999011^3597*400000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179728889 400000000 7156117999011 20000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4012214761/10000000000 : ℝ)^4621 ≤ (30936765919413/100000000000000 : ℝ)^3597 := by
    have hnat : (4012214761 : ℕ)^4621*100000000000000^3597 ≤ 30936765919413^3597*10000000000^4621 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012214761 10000000000 30936765919413 100000000000000 4621 3597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4621/1024 : ℝ)) 4621 3597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061776121/2500000000 : ℝ), (179728889/400000000 : ℝ), (4012214761/10000000000 : ℝ)] ![(4160330507469/12500000000000 : ℝ), (7156117999011/20000000000000 : ℝ), (30936765919413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061776121/2500000000 : ℝ)|^4621 ≤ (4160330507469/12500000000000 : ℝ)^3597
        have hw : |(1061776121/2500000000 : ℝ)|=(1061776121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179728889/400000000 : ℝ)|^4621 ≤ (7156117999011/20000000000000 : ℝ)^3597
        have hw : |(179728889/400000000 : ℝ)|=(179728889/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4012214761/10000000000 : ℝ)|^4621 ≤ (30936765919413/100000000000000 : ℝ)^3597
        have hw : |(4012214761/10000000000 : ℝ)|=(4012214761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1562_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2219/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2773/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2773/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2773/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2773/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2773/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2773/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2773/25000 : ℝ) ^ (4619/1024 : ℝ) ≤ (4923633194042137/100000000000000000000 : ℝ) := by
    have hpowers : (2773/25000 : ℝ)^4619 ≤ (4923633194042137/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2773 : ℕ)^4619*100000000000000000000^1024 ≤ 4923633194042137^1024*25000^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2773 25000 4923633194042137 100000000000000000000 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2773/25000 : ℝ)) (X := (4923633194042137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4619/1024 : ℝ) ≤ (22202623181177511/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4619 ≤ (22202623181177511/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4619*100000000000000000000^1024 ≤ 22202623181177511^1024*100000^4619 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 22202623181177511 100000000000000000000 4619 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (22202623181177511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004923633194042137/50000000000000000000 : ℝ) ≤ (10000218298644523/10000000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (50004923633194042137/50000000000000000000 : ℝ)^1024 ≤ (10000218298644523/10000000000000000 : ℝ)^4619 := by
      have hnat : (50004923633194042137 : ℕ)^1024*10000000000000000^4619 ≤ 10000218298644523^4619*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004923633194042137 50000000000000000000 10000218298644523 10000000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000218298644523/10000000000000000 : ℝ)) (X := (50004923633194042137/50000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1562923847755862807/1562500000000000000 : ℝ) ≤ (2000120261332549/2000000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (1562923847755862807/1562500000000000000 : ℝ)^1024 ≤ (2000120261332549/2000000000000000 : ℝ)^4619 := by
      have hnat : (1562923847755862807 : ℕ)^1024*2000000000000000^4619 ≤ 2000120261332549^4619*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562923847755862807 1562500000000000000 2000120261332549 2000000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000120261332549/2000000000000000 : ℝ)) (X := (1562923847755862807/1562500000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022202623181177511/50000000000000000000 : ℝ) ≤ (10000984314680967/10000000000000000 : ℝ) ^ (4619/1024 : ℝ) := by
    have hpowers : (50022202623181177511/50000000000000000000 : ℝ)^1024 ≤ (10000984314680967/10000000000000000 : ℝ)^4619 := by
      have hnat : (50022202623181177511 : ℕ)^1024*10000000000000000^4619 ≤ 10000984314680967^4619*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022202623181177511 50000000000000000000 10000984314680967 10000000000000000 1024 4619 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000984314680967/10000000000000000 : ℝ)) (X := (50022202623181177511/50000000000000000000 : ℝ)) (by norm_num) 4619 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4923633194042137/100000000000000000000 : ℝ) ≤ ((43962463209263730783/43970000000000000000 : ℝ)+2*(191504009111/219850000000000 : ℝ)*(2773/25000 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (43962463209263730783/43970000000000000000 : ℝ)+2*(191504009111/219850000000000 : ℝ)*(2773/25000 : ℝ)=(10000218298644523/10000000000000000 : ℝ) by norm_num, show 1+2*(4923633194042137/100000000000000000000 : ℝ)=(50004923633194042137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22202623181177511/100000000000000000000 : ℝ)+(4923633194042137/100000000000000000000 : ℝ) ≤ ((43962463209263730783/43970000000000000000 : ℝ)+(191504009111/219850000000000 : ℝ)*((15489/100000 : ℝ)+(2773/25000 : ℝ)))^(4619/1024 : ℝ) := by
    rw [show (43962463209263730783/43970000000000000000 : ℝ)+(191504009111/219850000000000 : ℝ)*((15489/100000 : ℝ)+(2773/25000 : ℝ))=(2000120261332549/2000000000000000 : ℝ) by norm_num, show 1+(22202623181177511/100000000000000000000 : ℝ)+(4923633194042137/100000000000000000000 : ℝ)=(1562923847755862807/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22202623181177511/100000000000000000000 : ℝ) ≤ ((43962463209263730783/43970000000000000000 : ℝ)+2*(191504009111/219850000000000 : ℝ)*(15489/100000 : ℝ))^(4619/1024 : ℝ) := by
    rw [show (43962463209263730783/43970000000000000000 : ℝ)+2*(191504009111/219850000000000 : ℝ)*(15489/100000 : ℝ)=(10000984314680967/10000000000000000 : ℝ) by norm_num, show 1+2*(22202623181177511/100000000000000000000 : ℝ)=(50022202623181177511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43962463209263730783/43970000000000000000 : ℝ)*(X 1 0+X 2 0)+(191504009111/219850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (2773/25000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (43962463209263730783/43970000000000000000 : ℝ)) (alpha := (191504009111/219850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43962463209263730783/43970000000000000000 : ℝ)*(X 0 1+X 2 1)+(191504009111/219850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (2773/25000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (43962463209263730783/43970000000000000000 : ℝ)) (alpha := (191504009111/219850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43962463209263730783/43970000000000000000 : ℝ)*(X 0 2+X 1 2)+(191504009111/219850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4619/1024 : ℝ)) (lo := (2773/25000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (43962463209263730783/43970000000000000000 : ℝ)) (alpha := (191504009111/219850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1796598977/10000000000 : ℝ)*X 0 0+(2713409289/5000000000 : ℝ)*X 0 1+(326235797/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348682957/10000000000 : ℝ)*X 1 0+(-1902536247/10000000000 : ℝ)*X 1 1+(5219772739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66858537/125000000 : ℝ)*X 2 0+(2609886367/5000000000 : ℝ)*X 2 1+(-1902536249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2123520463/5000000000 : ℝ)*X 0 0+(4009668149/10000000000 : ℝ)*X 0 1+(2247875091/5000000000 : ℝ)*X 0 2+(2123520463/5000000000 : ℝ)*X 1 0+(4009668149/10000000000 : ℝ)*X 1 1+(2247875091/5000000000 : ℝ)*X 1 2+(2123520463/5000000000 : ℝ)*X 2 0+(4009668149/10000000000 : ℝ)*X 2 1+(2247875091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-449156509/2500000000 : ℝ)*X 0 0+(5220849527/10000000000 : ℝ)*X 0 1+(2712866923/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293957919/10000000000 : ℝ)*X 1 0+(-339315031/2000000000 : ℝ)*X 1 1+(2712866923/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293957919/10000000000 : ℝ)*X 2 0+(2712866923/5000000000 : ℝ)*X 2 1+(-339315031/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1061776121/2500000000 : ℝ)*X 0 0+(179728889/400000000 : ℝ)*X 0 1+(4012214761/10000000000 : ℝ)*X 0 2+(1061776121/2500000000 : ℝ)*X 1 0+(179728889/400000000 : ℝ)*X 1 1+(4012214761/10000000000 : ℝ)*X 1 2+(1061776121/2500000000 : ℝ)*X 2 0+(179728889/400000000 : ℝ)*X 2 1+(4012214761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1562_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1301780316498792364524351147/219850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1017870319/100000000000000 : ℝ)*(base19) + (193140389/20000000000000 : ℝ)*(base23) + (29352173/100000000000000 : ℝ)*(lower2) + (140357803/100000000000000 : ℝ)*(upper3) + (98957199/100000000000000 : ℝ)*(upper5) + (344358129659097/10000000000000 : ℝ)*(major0) + (344358129659097/10000000000000 : ℝ)*(major1) + (344358129659097/10000000000000 : ℝ)*(major2) + (603733205658339/12500000000000 : ℝ)*(sp0) + (75466892685887/1562500000000 : ℝ)*(sp1) + (2414940592032571/50000000000000 : ℝ)*(sp2) + (51431818227867/2500000000000 : ℝ)*(sp3) + (8252250187/50000000000000 : ℝ)*(sp4) + (1879231537/25000000000000 : ℝ)*(sp7) + (2057280246040829/100000000000000 : ℝ)*(f.failure) + (2414941074883543/50000000000000 : ℝ)*(f.sum) + (643438110193/219850000000000000000000000 : ℝ)*base66 + (2574840056544482951/439700000000000000000000000000000 : ℝ)*base67 + (5279141493353082951/439700000000000000000000000000000 : ℝ)*base69 + (1372680590705317049/439700000000000000000000000000000 : ℝ)*base72 + (44927398953/54962500000000000000000000 : ℝ)*base73 + (4678107770110282951/439700000000000000000000000000000 : ℝ)*base75 + (4213317302862117049/439700000000000000000000000000000 : ℝ)*base78 + (1662181327062682951/439700000000000000000000000000000 : ℝ)*base79 + (15934345514579/2198500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (65818043/5000000000000000000000 : ℝ)*base89 + (65818043/5000000000000000000000 : ℝ)*base91 + (65818043/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3713448289598546219250459789/549625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (532799527/50000000000000 : ℝ)*(base19) + (57788957/5000000000000 : ℝ)*(base23) + (347902271/100000000000000 : ℝ)*(lower1) + (139531091/100000000000000 : ℝ)*(upper3) + (5104741/12500000000000 : ℝ)*(lower4) + (3490077/2500000000000 : ℝ)*(upper5) + (1739936967648561/50000000000000 : ℝ)*(major0) + (1739936967648561/50000000000000 : ℝ)*(major1) + (1739936967648561/50000000000000 : ℝ)*(major2) + (252280283/20000000000000 : ℝ)*(sp2) + (976157056694101/20000000000000 : ℝ)*(sp4) + (4880784217871451/100000000000000 : ℝ)*(sp5) + (97615657325799/2000000000000 : ℝ)*(sp6) + (2078962361912691/100000000000000 : ℝ)*(sp7) + (2078962361912691/100000000000000 : ℝ)*(f.failure) + (976157056694101/20000000000000 : ℝ)*(f.sum) + (20274064644239/5496250000000000000000000000 : ℝ)*base66 + (54167122753430553263/2198500000000000000000000000000000 : ℝ)*base67 + (30830592754562946737/2198500000000000000000000000000000 : ℝ)*base70 + (148738418435714946737/2198500000000000000000000000000000 : ℝ)*base72 + (15306749490317/10992500000000000000000000000 : ℝ)*base73 + (176913483122288946737/2198500000000000000000000000000000 : ℝ)*base76 + (25045382495943446737/2198500000000000000000000000000000 : ℝ)*base78 + (33471606183806946737/2198500000000000000000000000000000 : ℝ)*base80 + (31845465992963/10992500000000000000000000000 : ℝ)*base82 + (39667797/5000000000000000000000 : ℝ)*base89 + (39667797/5000000000000000000000 : ℝ)*base91 + (39667797/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1562_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2219/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1562_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1562_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2219/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1562_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1562_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1562_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4619/1024 : ℝ) ≤ p) (hpb : p ≤ (4621/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83692567/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2219/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1562_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
