-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1449_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:57.861998+00:00
-- url     : https://prove2.me/submissions/475f752e-7acf-431f-8657-d60946946137

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
theorem support_rectangle_w1449_s6_0 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-977509521/5000000000 : ℝ)*x 0 + (2703594893/5000000000 : ℝ)*x 1 + (209893337/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977509521/5000000000 : ℝ)^4409 ≤ (11932084327753/100000000000000 : ℝ)^3385 := by
    have hnat : (977509521 : ℕ)^4409*100000000000000^3385 ≤ 11932084327753^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977509521 5000000000 11932084327753 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703594893/5000000000 : ℝ)^4409 ≤ (44894440944453/100000000000000 : ℝ)^3385 := by
    have hnat : (2703594893 : ℕ)^4409*100000000000000^3385 ≤ 44894440944453^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703594893 5000000000 44894440944453 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209893337/400000000 : ℝ)^4409 ≤ (43173474718079/100000000000000 : ℝ)^3385 := by
    have hnat : (209893337 : ℕ)^4409*100000000000000^3385 ≤ 43173474718079^3385*400000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209893337 400000000 43173474718079 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977509521/5000000000 : ℝ), (2703594893/5000000000 : ℝ), (209893337/400000000 : ℝ)] ![(11932084327753/100000000000000 : ℝ), (44894440944453/100000000000000 : ℝ), (43173474718079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977509521/5000000000 : ℝ)|^4409 ≤ (11932084327753/100000000000000 : ℝ)^3385
        have hw : |(-977509521/5000000000 : ℝ)|=(977509521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703594893/5000000000 : ℝ)|^4409 ≤ (44894440944453/100000000000000 : ℝ)^3385
        have hw : |(2703594893/5000000000 : ℝ)|=(2703594893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209893337/400000000 : ℝ)|^4409 ≤ (43173474718079/100000000000000 : ℝ)^3385
        have hw : |(209893337/400000000 : ℝ)|=(209893337/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s6_1 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336724659/2500000000 : ℝ)*x 0 + (-407278169/2000000000 : ℝ)*x 1 + (40994793/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336724659/2500000000 : ℝ)^4409 ≤ (2765220681603/6250000000000 : ℝ)^3385 := by
    have hnat : (1336724659 : ℕ)^4409*6250000000000^3385 ≤ 2765220681603^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336724659 2500000000 2765220681603 6250000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (407278169/2000000000 : ℝ)^4409 ≤ (125829935183/1000000000000 : ℝ)^3385 := by
    have hnat : (407278169 : ℕ)^4409*1000000000000^3385 ≤ 125829935183^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407278169 2000000000 125829935183 1000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40994793/78125000 : ℝ)^4409 ≤ (8634695112939/20000000000000 : ℝ)^3385 := by
    have hnat : (40994793 : ℕ)^4409*20000000000000^3385 ≤ 8634695112939^3385*78125000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40994793 78125000 8634695112939 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336724659/2500000000 : ℝ), (-407278169/2000000000 : ℝ), (40994793/78125000 : ℝ)] ![(2765220681603/6250000000000 : ℝ), (125829935183/1000000000000 : ℝ), (8634695112939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336724659/2500000000 : ℝ)|^4409 ≤ (2765220681603/6250000000000 : ℝ)^3385
        have hw : |(1336724659/2500000000 : ℝ)|=(1336724659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-407278169/2000000000 : ℝ)|^4409 ≤ (125829935183/1000000000000 : ℝ)^3385
        have hw : |(-407278169/2000000000 : ℝ)|=(407278169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40994793/78125000 : ℝ)|^4409 ≤ (8634695112939/20000000000000 : ℝ)^3385
        have hw : |(40994793/78125000 : ℝ)|=(40994793/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s6_2 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346899087/10000000000 : ℝ)*x 0 + (2623666789/5000000000 : ℝ)*x 1 + (-1018195071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346899087/10000000000 : ℝ)^4409 ≤ (22121767883213/50000000000000 : ℝ)^3385 := by
    have hnat : (5346899087 : ℕ)^4409*50000000000000^3385 ≤ 22121767883213^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346899087 10000000000 22121767883213 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623666789/5000000000 : ℝ)^4409 ≤ (43173476357729/100000000000000 : ℝ)^3385 := by
    have hnat : (2623666789 : ℕ)^4409*100000000000000^3385 ≤ 43173476357729^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623666789 5000000000 43173476357729 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1018195071/5000000000 : ℝ)^4409 ≤ (1572873482543/12500000000000 : ℝ)^3385 := by
    have hnat : (1018195071 : ℕ)^4409*12500000000000^3385 ≤ 1572873482543^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018195071 5000000000 1572873482543 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346899087/10000000000 : ℝ), (2623666789/5000000000 : ℝ), (-1018195071/5000000000 : ℝ)] ![(22121767883213/50000000000000 : ℝ), (43173476357729/100000000000000 : ℝ), (1572873482543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346899087/10000000000 : ℝ)|^4409 ≤ (22121767883213/50000000000000 : ℝ)^3385
        have hw : |(5346899087/10000000000 : ℝ)|=(5346899087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623666789/5000000000 : ℝ)|^4409 ≤ (43173476357729/100000000000000 : ℝ)^3385
        have hw : |(2623666789/5000000000 : ℝ)|=(2623666789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1018195071/5000000000 : ℝ)|^4409 ≤ (1572873482543/12500000000000 : ℝ)^3385
        have hw : |(-1018195071/5000000000 : ℝ)|=(1018195071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s6_3 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149698917/5000000000 : ℝ)*x 0 + (412836353/1000000000 : ℝ)*x 1 + (895344631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149698917/5000000000 : ℝ)^4409 ≤ (6660999128843/20000000000000 : ℝ)^3385 := by
    have hnat : (2149698917 : ℕ)^4409*20000000000000^3385 ≤ 6660999128843^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149698917 5000000000 6660999128843 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412836353/1000000000 : ℝ)^4409 ≤ (31589772699031/100000000000000 : ℝ)^3385 := by
    have hnat : (412836353 : ℕ)^4409*100000000000000^3385 ≤ 31589772699031^3385*1000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412836353 1000000000 31589772699031 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895344631/2000000000 : ℝ)^4409 ≤ (17552615828061/50000000000000 : ℝ)^3385 := by
    have hnat : (895344631 : ℕ)^4409*50000000000000^3385 ≤ 17552615828061^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895344631 2000000000 17552615828061 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149698917/5000000000 : ℝ), (412836353/1000000000 : ℝ), (895344631/2000000000 : ℝ)] ![(6660999128843/20000000000000 : ℝ), (31589772699031/100000000000000 : ℝ), (17552615828061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149698917/5000000000 : ℝ)|^4409 ≤ (6660999128843/20000000000000 : ℝ)^3385
        have hw : |(2149698917/5000000000 : ℝ)|=(2149698917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(412836353/1000000000 : ℝ)|^4409 ≤ (31589772699031/100000000000000 : ℝ)^3385
        have hw : |(412836353/1000000000 : ℝ)|=(412836353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895344631/2000000000 : ℝ)|^4409 ≤ (17552615828061/50000000000000 : ℝ)^3385
        have hw : |(895344631/2000000000 : ℝ)|=(895344631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s6_4 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1955029491/10000000000 : ℝ)*x 0 + (65598889/125000000 : ℝ)*x 1 + (5406609611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1955029491/10000000000 : ℝ)^4409 ≤ (186440115523/1562500000000 : ℝ)^3385 := by
    have hnat : (1955029491 : ℕ)^4409*1562500000000^3385 ≤ 186440115523^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955029491 10000000000 186440115523 1562500000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65598889/125000000 : ℝ)^4409 ≤ (43179665786569/100000000000000 : ℝ)^3385 := by
    have hnat : (65598889 : ℕ)^4409*100000000000000^3385 ≤ 43179665786569^3385*125000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65598889 125000000 43179665786569 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406609611/10000000000 : ℝ)^4409 ≤ (1402755212577/3125000000000 : ℝ)^3385 := by
    have hnat : (5406609611 : ℕ)^4409*3125000000000^3385 ≤ 1402755212577^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406609611 10000000000 1402755212577 3125000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1955029491/10000000000 : ℝ), (65598889/125000000 : ℝ), (5406609611/10000000000 : ℝ)] ![(186440115523/1562500000000 : ℝ), (43179665786569/100000000000000 : ℝ), (1402755212577/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1955029491/10000000000 : ℝ)|^4409 ≤ (186440115523/1562500000000 : ℝ)^3385
        have hw : |(-1955029491/10000000000 : ℝ)|=(1955029491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65598889/125000000 : ℝ)|^4409 ≤ (43179665786569/100000000000000 : ℝ)^3385
        have hw : |(65598889/125000000 : ℝ)|=(65598889/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406609611/10000000000 : ℝ)|^4409 ≤ (1402755212577/3125000000000 : ℝ)^3385
        have hw : |(5406609611/10000000000 : ℝ)|=(5406609611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s6_5 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305260539/10000000000 : ℝ)*x 0 + (-375422871/2000000000 : ℝ)*x 1 + (5406609593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305260539/10000000000 : ℝ)^4409 ≤ (10948823567757/25000000000000 : ℝ)^3385 := by
    have hnat : (5305260539 : ℕ)^4409*25000000000000^3385 ≤ 10948823567757^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305260539 10000000000 10948823567757 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375422871/2000000000 : ℝ)^4409 ≤ (5658269553223/50000000000000 : ℝ)^3385 := by
    have hnat : (375422871 : ℕ)^4409*50000000000000^3385 ≤ 5658269553223^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375422871 2000000000 5658269553223 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406609593/10000000000 : ℝ)^4409 ≤ (44888166607811/100000000000000 : ℝ)^3385 := by
    have hnat : (5406609593 : ℕ)^4409*100000000000000^3385 ≤ 44888166607811^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406609593 10000000000 44888166607811 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305260539/10000000000 : ℝ), (-375422871/2000000000 : ℝ), (5406609593/10000000000 : ℝ)] ![(10948823567757/25000000000000 : ℝ), (5658269553223/50000000000000 : ℝ), (44888166607811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305260539/10000000000 : ℝ)|^4409 ≤ (10948823567757/25000000000000 : ℝ)^3385
        have hw : |(5305260539/10000000000 : ℝ)|=(5305260539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375422871/2000000000 : ℝ)|^4409 ≤ (5658269553223/50000000000000 : ℝ)^3385
        have hw : |(-375422871/2000000000 : ℝ)|=(375422871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406609593/10000000000 : ℝ)|^4409 ≤ (44888166607811/100000000000000 : ℝ)^3385
        have hw : |(5406609593/10000000000 : ℝ)|=(5406609593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s6_6 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326315113/2500000000 : ℝ)*x 0 + (108132193/200000000 : ℝ)*x 1 + (-469278599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326315113/2500000000 : ℝ)^4409 ≤ (5474411666947/12500000000000 : ℝ)^3385 := by
    have hnat : (1326315113 : ℕ)^4409*12500000000000^3385 ≤ 5474411666947^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326315113 2500000000 5474411666947 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108132193/200000000 : ℝ)^4409 ≤ (44888167224211/100000000000000 : ℝ)^3385 := by
    have hnat : (108132193 : ℕ)^4409*100000000000000^3385 ≤ 44888167224211^3385*200000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108132193 200000000 44888167224211 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469278599/2500000000 : ℝ)^4409 ≤ (2829134857099/25000000000000 : ℝ)^3385 := by
    have hnat : (469278599 : ℕ)^4409*25000000000000^3385 ≤ 2829134857099^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469278599 2500000000 2829134857099 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326315113/2500000000 : ℝ), (108132193/200000000 : ℝ), (-469278599/2500000000 : ℝ)] ![(5474411666947/12500000000000 : ℝ), (44888167224211/100000000000000 : ℝ), (2829134857099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326315113/2500000000 : ℝ)|^4409 ≤ (5474411666947/12500000000000 : ℝ)^3385
        have hw : |(1326315113/2500000000 : ℝ)|=(1326315113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108132193/200000000 : ℝ)|^4409 ≤ (44888167224211/100000000000000 : ℝ)^3385
        have hw : |(108132193/200000000 : ℝ)|=(108132193/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-469278599/2500000000 : ℝ)|^4409 ≤ (2829134857099/25000000000000 : ℝ)^3385
        have hw : |(-469278599/2500000000 : ℝ)|=(469278599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s6_7 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4299421577/10000000000 : ℝ)*x 0 + (111886611/250000000 : ℝ)*x 1 + (2064814661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299421577/10000000000 : ℝ)^4409 ≤ (8326308801719/25000000000000 : ℝ)^3385 := by
    have hnat : (4299421577 : ℕ)^4409*25000000000000^3385 ≤ 8326308801719^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299421577 10000000000 8326308801719 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111886611/250000000 : ℝ)^4409 ≤ (4386546971433/12500000000000 : ℝ)^3385 := by
    have hnat : (111886611 : ℕ)^4409*12500000000000^3385 ≤ 4386546971433^3385*250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111886611 250000000 4386546971433 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064814661/5000000000 : ℝ)^4409 ≤ (31602389012747/100000000000000 : ℝ)^3385 := by
    have hnat : (2064814661 : ℕ)^4409*100000000000000^3385 ≤ 31602389012747^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064814661 5000000000 31602389012747 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299421577/10000000000 : ℝ), (111886611/250000000 : ℝ), (2064814661/5000000000 : ℝ)] ![(8326308801719/25000000000000 : ℝ), (4386546971433/12500000000000 : ℝ), (31602389012747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299421577/10000000000 : ℝ)|^4409 ≤ (8326308801719/25000000000000 : ℝ)^3385
        have hw : |(4299421577/10000000000 : ℝ)|=(4299421577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(111886611/250000000 : ℝ)|^4409 ≤ (4386546971433/12500000000000 : ℝ)^3385
        have hw : |(111886611/250000000 : ℝ)|=(111886611/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064814661/5000000000 : ℝ)|^4409 ≤ (31602389012747/100000000000000 : ℝ)^3385
        have hw : |(2064814661/5000000000 : ℝ)|=(2064814661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1449_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (569/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11377/100000 : ℝ) ^ (551/128 : ℝ) ≤ (4319808495490313/50000000000000000000 : ℝ) := by
    have hpowers : (11377/100000 : ℝ)^551 ≤ (4319808495490313/50000000000000000000 : ℝ)^128 := by
      have hnat : (11377 : ℕ)^551*50000000000000000000^128 ≤ 4319808495490313^128*100000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11377 100000 4319808495490313 50000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11377/100000 : ℝ)) (X := (4319808495490313/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hpowhi : (1477/10000 : ℝ) ^ (551/128 : ℝ) ≤ (26573123192558301/100000000000000000000 : ℝ) := by
    have hpowers : (1477/10000 : ℝ)^551 ≤ (26573123192558301/100000000000000000000 : ℝ)^128 := by
      have hnat : (1477 : ℕ)^551*100000000000000000000^128 ≤ 26573123192558301^128*10000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 10000 26573123192558301 100000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/10000 : ℝ)) (X := (26573123192558301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004319808495490313/25000000000000000000 : ℝ) ≤ (10000401378451691/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (25004319808495490313/25000000000000000000 : ℝ)^128 ≤ (10000401378451691/10000000000000000 : ℝ)^551 := by
      have hnat : (25004319808495490313 : ℕ)^128*10000000000000000^551 ≤ 10000401378451691^551*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004319808495490313 25000000000000000000 10000401378451691 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000401378451691/10000000000000000 : ℝ)) (X := (25004319808495490313/25000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035212740183538927/100000000000000000000 : ℝ) ≤ (2000163579733501/2000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (100035212740183538927/100000000000000000000 : ℝ)^128 ≤ (2000163579733501/2000000000000000 : ℝ)^551 := by
      have hnat : (100035212740183538927 : ℕ)^128*2000000000000000^551 ≤ 2000163579733501^551*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035212740183538927 100000000000000000000 2000163579733501 2000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000163579733501/2000000000000000 : ℝ)) (X := (100035212740183538927/100000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026573123192558301/50000000000000000000 : ℝ) ≤ (10001234418883319/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (50026573123192558301/50000000000000000000 : ℝ)^128 ≤ (10001234418883319/10000000000000000 : ℝ)^551 := by
      have hnat : (50026573123192558301 : ℕ)^128*10000000000000000^551 ≤ 10001234418883319^551*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026573123192558301 50000000000000000000 10001234418883319 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001234418883319/10000000000000000 : ℝ)) (X := (50026573123192558301/50000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4319808495490313/50000000000000000000 : ℝ) ≤ ((11307294792031985269/11310000000000000000 : ℝ)+2*(69420035969/56550000000000 : ℝ)*(11377/100000 : ℝ))^(551/128 : ℝ) := by
    rw [show (11307294792031985269/11310000000000000000 : ℝ)+2*(69420035969/56550000000000 : ℝ)*(11377/100000 : ℝ)=(10000401378451691/10000000000000000 : ℝ) by norm_num, show 1+2*(4319808495490313/50000000000000000000 : ℝ)=(25004319808495490313/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26573123192558301/100000000000000000000 : ℝ)+(4319808495490313/50000000000000000000 : ℝ) ≤ ((11307294792031985269/11310000000000000000 : ℝ)+(69420035969/56550000000000 : ℝ)*((1477/10000 : ℝ)+(11377/100000 : ℝ)))^(551/128 : ℝ) := by
    rw [show (11307294792031985269/11310000000000000000 : ℝ)+(69420035969/56550000000000 : ℝ)*((1477/10000 : ℝ)+(11377/100000 : ℝ))=(2000163579733501/2000000000000000 : ℝ) by norm_num, show 1+(26573123192558301/100000000000000000000 : ℝ)+(4319808495490313/50000000000000000000 : ℝ)=(100035212740183538927/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26573123192558301/100000000000000000000 : ℝ) ≤ ((11307294792031985269/11310000000000000000 : ℝ)+2*(69420035969/56550000000000 : ℝ)*(1477/10000 : ℝ))^(551/128 : ℝ) := by
    rw [show (11307294792031985269/11310000000000000000 : ℝ)+2*(69420035969/56550000000000 : ℝ)*(1477/10000 : ℝ)=(10001234418883319/10000000000000000 : ℝ) by norm_num, show 1+2*(26573123192558301/100000000000000000000 : ℝ)=(50026573123192558301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11307294792031985269/11310000000000000000 : ℝ)*(X 1 0+X 2 0)+(69420035969/56550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (11307294792031985269/11310000000000000000 : ℝ)) (alpha := (69420035969/56550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11307294792031985269/11310000000000000000 : ℝ)*(X 0 1+X 2 1)+(69420035969/56550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (11307294792031985269/11310000000000000000 : ℝ)) (alpha := (69420035969/56550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11307294792031985269/11310000000000000000 : ℝ)*(X 0 2+X 1 2)+(69420035969/56550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (11307294792031985269/11310000000000000000 : ℝ)) (alpha := (69420035969/56550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-977509521/5000000000 : ℝ)*X 0 0+(2703594893/5000000000 : ℝ)*X 0 1+(209893337/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336724659/2500000000 : ℝ)*X 1 0+(-407278169/2000000000 : ℝ)*X 1 1+(40994793/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346899087/10000000000 : ℝ)*X 2 0+(2623666789/5000000000 : ℝ)*X 2 1+(-1018195071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149698917/5000000000 : ℝ)*X 0 0+(412836353/1000000000 : ℝ)*X 0 1+(895344631/2000000000 : ℝ)*X 0 2+(2149698917/5000000000 : ℝ)*X 1 0+(412836353/1000000000 : ℝ)*X 1 1+(895344631/2000000000 : ℝ)*X 1 2+(2149698917/5000000000 : ℝ)*X 2 0+(412836353/1000000000 : ℝ)*X 2 1+(895344631/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1955029491/10000000000 : ℝ)*X 0 0+(65598889/125000000 : ℝ)*X 0 1+(5406609611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305260539/10000000000 : ℝ)*X 1 0+(-375422871/2000000000 : ℝ)*X 1 1+(5406609593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326315113/2500000000 : ℝ)*X 2 0+(108132193/200000000 : ℝ)*X 2 1+(-469278599/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4299421577/10000000000 : ℝ)*X 0 0+(111886611/250000000 : ℝ)*X 0 1+(2064814661/5000000000 : ℝ)*X 0 2+(4299421577/10000000000 : ℝ)*X 1 0+(111886611/250000000 : ℝ)*X 1 1+(2064814661/5000000000 : ℝ)*X 1 2+(4299421577/10000000000 : ℝ)*X 2 0+(111886611/250000000 : ℝ)*X 2 1+(2064814661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (160261592707933187366008563/23562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1186132491/50000000000000 : ℝ)*(base19) + (2506799207/100000000000000 : ℝ)*(base23) + (84223/125000000000 : ℝ)*(upper3) + (52549659/25000000000000 : ℝ)*(upper4) + (781271877/100000000000000 : ℝ)*(upper5) + (570398117672727/12500000000000 : ℝ)*(major0) + (570398117672727/12500000000000 : ℝ)*(major1) + (570398117672727/12500000000000 : ℝ)*(major2) + (6255647331698949/100000000000000 : ℝ)*(sp0) + (6255714618321581/100000000000000 : ℝ)*(sp1) + (6255714483787357/100000000000000 : ℝ)*(sp2) + (358828518689013/12500000000000 : ℝ)*(sp3) + (13931777523/20000000000000 : ℝ)*(sp4) + (24515946519/100000000000000 : ℝ)*(sp7) + (44853947897791/1562500000000 : ℝ)*(f.failure) + (6255716990586563/100000000000000 : ℝ)*(f.sum) + (1124209989297/235625000000000000000000000 : ℝ)*base65 + (42961657076463883/3625000000000000000000000000000 : ℝ)*base68 + (34282577437213883/3625000000000000000000000000000 : ℝ)*base70 + (56735552409911117/3625000000000000000000000000000 : ℝ)*base71 + (9826429940339/1885000000000000000000000000 : ℝ)*base74 + (20778044972963883/3625000000000000000000000000000 : ℝ)*base76 + (8207026566536117/3625000000000000000000000000000 : ℝ)*base77 + (51478448242463883/3625000000000000000000000000000 : ℝ)*base80 + (615122198413/235625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1004511/78125000000000000000 : ℝ)*base89 + (1004511/78125000000000000000 : ℝ)*base91 + (1004511/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1223829634004062502386063791/188500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (276040473/25000000000000 : ℝ)*(base19) + (561673117/50000000000000 : ℝ)*(base23) + (392609329/100000000000000 : ℝ)*(lower1) + (18982853/20000000000000 : ℝ)*(upper3) + (33586609/50000000000000 : ℝ)*(lower4) + (1318621/1000000000000 : ℝ)*(upper5) + (4596385062816913/100000000000000 : ℝ)*(major0) + (4596385062816913/100000000000000 : ℝ)*(major1) + (4596385062816913/100000000000000 : ℝ)*(major2) + (104458299/20000000000000 : ℝ)*(sp1) + (6301231389183231/100000000000000 : ℝ)*(sp4) + (1575307440682461/25000000000000 : ℝ)*(sp5) + (6301230265836997/100000000000000 : ℝ)*(sp6) + (180721157502193/6250000000000 : ℝ)*(sp7) + (180721157502193/6250000000000 : ℝ)*(f.failure) + (6301231389183231/100000000000000 : ℝ)*(f.sum) + (8817790260131/5655000000000000000000000000 : ℝ)*base66 + (1823414683156965031/87000000000000000000000000000000 : ℝ)*base68 + (1848051694375965031/87000000000000000000000000000000 : ℝ)*base70 + (1307906716420965031/87000000000000000000000000000000 : ℝ)*base72 + (18776066957981/5655000000000000000000000000 : ℝ)*base74 + (1051210762672965031/87000000000000000000000000000000 : ℝ)*base76 + (469384700416965031/87000000000000000000000000000000 : ℝ)*base78 + (746771615866965031/87000000000000000000000000000000 : ℝ)*base80 + (6328522115413/2827500000000000000000000000 : ℝ)*base82 + (3841753/312500000000000000000 : ℝ)*base89 + (3841753/312500000000000000000 : ℝ)*base91 + (3841753/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1449_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1449_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1449_s7_0 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-3128037/16000000 : ℝ)*x 0 + (5407167799/10000000000 : ℝ)*x 1 + (655919073/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3128037/16000000 : ℝ)^4409 ≤ (1193211678609/10000000000000 : ℝ)^3385 := by
    have hnat : (3128037 : ℕ)^4409*10000000000000^3385 ≤ 1193211678609^3385*16000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3128037 16000000 1193211678609 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407167799/10000000000 : ℝ)^4409 ≤ (44894203168413/100000000000000 : ℝ)^3385 := by
    have hnat : (5407167799 : ℕ)^4409*100000000000000^3385 ≤ 44894203168413^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407167799 10000000000 44894203168413 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655919073/1250000000 : ℝ)^4409 ≤ (4317368003883/10000000000000 : ℝ)^3385 := by
    have hnat : (655919073 : ℕ)^4409*10000000000000^3385 ≤ 4317368003883^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655919073 1250000000 4317368003883 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3128037/16000000 : ℝ), (5407167799/10000000000 : ℝ), (655919073/1250000000 : ℝ)] ![(1193211678609/10000000000000 : ℝ), (44894203168413/100000000000000 : ℝ), (4317368003883/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3128037/16000000 : ℝ)|^4409 ≤ (1193211678609/10000000000000 : ℝ)^3385
        have hw : |(-3128037/16000000 : ℝ)|=(3128037/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407167799/10000000000 : ℝ)|^4409 ≤ (44894203168413/100000000000000 : ℝ)^3385
        have hw : |(5407167799/10000000000 : ℝ)|=(5407167799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655919073/1250000000 : ℝ)|^4409 ≤ (4317368003883/10000000000000 : ℝ)^3385
        have hw : |(655919073/1250000000 : ℝ)|=(655919073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s7_1 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336723943/2500000000 : ℝ)*x 0 + (-81454931/400000000 : ℝ)*x 1 + (5247349579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336723943/2500000000 : ℝ)^4409 ≤ (44243500038093/100000000000000 : ℝ)^3385 := by
    have hnat : (1336723943 : ℕ)^4409*100000000000000^3385 ≤ 44243500038093^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336723943 2500000000 44243500038093 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81454931/400000000 : ℝ)^4409 ≤ (12582852109819/100000000000000 : ℝ)^3385 := by
    have hnat : (81454931 : ℕ)^4409*100000000000000^3385 ≤ 12582852109819^3385*400000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81454931 400000000 12582852109819 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247349579/10000000000 : ℝ)^4409 ≤ (43173647835211/100000000000000 : ℝ)^3385 := by
    have hnat : (5247349579 : ℕ)^4409*100000000000000^3385 ≤ 43173647835211^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247349579 10000000000 43173647835211 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336723943/2500000000 : ℝ), (-81454931/400000000 : ℝ), (5247349579/10000000000 : ℝ)] ![(44243500038093/100000000000000 : ℝ), (12582852109819/100000000000000 : ℝ), (43173647835211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336723943/2500000000 : ℝ)|^4409 ≤ (44243500038093/100000000000000 : ℝ)^3385
        have hw : |(1336723943/2500000000 : ℝ)|=(1336723943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-81454931/400000000 : ℝ)|^4409 ≤ (12582852109819/100000000000000 : ℝ)^3385
        have hw : |(-81454931/400000000 : ℝ)|=(81454931/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247349579/10000000000 : ℝ)|^4409 ≤ (43173647835211/100000000000000 : ℝ)^3385
        have hw : |(5247349579/10000000000 : ℝ)|=(5247349579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s7_2 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534689341/1000000000 : ℝ)*x 0 + (5247353703/10000000000 : ℝ)*x 1 + (-2036370947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534689341/1000000000 : ℝ)^4409 ≤ (22121737290493/50000000000000 : ℝ)^3385 := by
    have hnat : (534689341 : ℕ)^4409*50000000000000^3385 ≤ 22121737290493^3385*1000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534689341 1000000000 22121737290493 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247353703/10000000000 : ℝ)^4409 ≤ (8634738406159/20000000000000 : ℝ)^3385 := by
    have hnat : (5247353703 : ℕ)^4409*20000000000000^3385 ≤ 8634738406159^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247353703 10000000000 8634738406159 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2036370947/10000000000 : ℝ)^4409 ≤ (786427085839/6250000000000 : ℝ)^3385 := by
    have hnat : (2036370947 : ℕ)^4409*6250000000000^3385 ≤ 786427085839^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036370947 10000000000 786427085839 6250000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534689341/1000000000 : ℝ), (5247353703/10000000000 : ℝ), (-2036370947/10000000000 : ℝ)] ![(22121737290493/50000000000000 : ℝ), (8634738406159/20000000000000 : ℝ), (786427085839/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534689341/1000000000 : ℝ)|^4409 ≤ (22121737290493/50000000000000 : ℝ)^3385
        have hw : |(534689341/1000000000 : ℝ)|=(534689341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247353703/10000000000 : ℝ)|^4409 ≤ (8634738406159/20000000000000 : ℝ)^3385
        have hw : |(5247353703/10000000000 : ℝ)|=(5247353703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2036370947/10000000000 : ℝ)|^4409 ≤ (786427085839/6250000000000 : ℝ)^3385
        have hw : |(-2036370947/10000000000 : ℝ)|=(2036370947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s7_3 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4299396733/10000000000 : ℝ)*x 0 + (4128410561/10000000000 : ℝ)*x 1 + (1119169587/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299396733/10000000000 : ℝ)^4409 ≤ (3330498453533/10000000000000 : ℝ)^3385 := by
    have hnat : (4299396733 : ℕ)^4409*10000000000000^3385 ≤ 3330498453533^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299396733 10000000000 3330498453533 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128410561/10000000000 : ℝ)^4409 ≤ (7897560360551/25000000000000 : ℝ)^3385 := by
    have hnat : (4128410561 : ℕ)^4409*25000000000000^3385 ≤ 7897560360551^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128410561 10000000000 7897560360551 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119169587/2500000000 : ℝ)^4409 ≤ (35104774001091/100000000000000 : ℝ)^3385 := by
    have hnat : (1119169587 : ℕ)^4409*100000000000000^3385 ≤ 35104774001091^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119169587 2500000000 35104774001091 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299396733/10000000000 : ℝ), (4128410561/10000000000 : ℝ), (1119169587/2500000000 : ℝ)] ![(3330498453533/10000000000000 : ℝ), (7897560360551/25000000000000 : ℝ), (35104774001091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299396733/10000000000 : ℝ)|^4409 ≤ (3330498453533/10000000000000 : ℝ)^3385
        have hw : |(4299396733/10000000000 : ℝ)|=(4299396733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128410561/10000000000 : ℝ)|^4409 ≤ (7897560360551/25000000000000 : ℝ)^3385
        have hw : |(4128410561/10000000000 : ℝ)|=(4128410561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119169587/2500000000 : ℝ)|^4409 ≤ (35104774001091/100000000000000 : ℝ)^3385
        have hw : |(1119169587/2500000000 : ℝ)|=(1119169587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s7_4 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305265897/10000000000 : ℝ)*x 0 + (-1877136107/10000000000 : ℝ)*x 1 + (5406588471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305265897/10000000000 : ℝ)^4409 ≤ (10948837970491/25000000000000 : ℝ)^3385 := by
    have hnat : (5305265897 : ℕ)^4409*25000000000000^3385 ≤ 10948837970491^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305265897 10000000000 10948837970491 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1877136107/10000000000 : ℝ)^4409 ≤ (11316709912901/100000000000000 : ℝ)^3385 := by
    have hnat : (1877136107 : ℕ)^4409*100000000000000^3385 ≤ 11316709912901^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877136107 10000000000 11316709912901 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406588471/10000000000 : ℝ)^4409 ≤ (44887938193629/100000000000000 : ℝ)^3385 := by
    have hnat : (5406588471 : ℕ)^4409*100000000000000^3385 ≤ 44887938193629^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406588471 10000000000 44887938193629 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305265897/10000000000 : ℝ), (-1877136107/10000000000 : ℝ), (5406588471/10000000000 : ℝ)] ![(10948837970491/25000000000000 : ℝ), (11316709912901/100000000000000 : ℝ), (44887938193629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305265897/10000000000 : ℝ)|^4409 ≤ (10948837970491/25000000000000 : ℝ)^3385
        have hw : |(5305265897/10000000000 : ℝ)|=(5305265897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1877136107/10000000000 : ℝ)|^4409 ≤ (11316709912901/100000000000000 : ℝ)^3385
        have hw : |(-1877136107/10000000000 : ℝ)|=(1877136107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406588471/10000000000 : ℝ)|^4409 ≤ (44887938193629/100000000000000 : ℝ)^3385
        have hw : |(5406588471/10000000000 : ℝ)|=(5406588471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s7_5 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-803707/312500000 : ℝ)*x 0 + (2935738389/5000000000 : ℝ)*x 1 + (587137709/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (803707/312500000 : ℝ)^4409 ≤ (4234664199/10000000000000 : ℝ)^3385 := by
    have hnat : (803707 : ℕ)^4409*10000000000000^3385 ≤ 4234664199^3385*312500000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803707 312500000 4234664199 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2935738389/5000000000 : ℝ)^4409 ≤ (49979379305789/100000000000000 : ℝ)^3385 := by
    have hnat : (2935738389 : ℕ)^4409*100000000000000^3385 ≤ 49979379305789^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2935738389 5000000000 49979379305789 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587137709/1000000000 : ℝ)^4409 ≤ (49978274040059/100000000000000 : ℝ)^3385 := by
    have hnat : (587137709 : ℕ)^4409*100000000000000^3385 ≤ 49978274040059^3385*1000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587137709 1000000000 49978274040059 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-803707/312500000 : ℝ), (2935738389/5000000000 : ℝ), (587137709/1000000000 : ℝ)] ![(4234664199/10000000000000 : ℝ), (49979379305789/100000000000000 : ℝ), (49978274040059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-803707/312500000 : ℝ)|^4409 ≤ (4234664199/10000000000000 : ℝ)^3385
        have hw : |(-803707/312500000 : ℝ)|=(803707/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2935738389/5000000000 : ℝ)|^4409 ≤ (49979379305789/100000000000000 : ℝ)^3385
        have hw : |(2935738389/5000000000 : ℝ)|=(2935738389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(587137709/1000000000 : ℝ)|^4409 ≤ (49978274040059/100000000000000 : ℝ)^3385
        have hw : |(587137709/1000000000 : ℝ)|=(587137709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s7_6 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (246241923/2500000000 : ℝ)*x 0 + (-546848517/1250000000 : ℝ)*x 1 + (855761137/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246241923/2500000000 : ℝ)^4409 ≤ (2442817312171/50000000000000 : ℝ)^3385 := by
    have hnat : (246241923 : ℕ)^4409*50000000000000^3385 ≤ 2442817312171^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246241923 2500000000 2442817312171 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546848517/1250000000 : ℝ)^4409 ≤ (34067679147423/100000000000000 : ℝ)^3385 := by
    have hnat : (546848517 : ℕ)^4409*100000000000000^3385 ≤ 34067679147423^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546848517 1250000000 34067679147423 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (855761137/1250000000 : ℝ)^4409 ≤ (61046686215713/100000000000000 : ℝ)^3385 := by
    have hnat : (855761137 : ℕ)^4409*100000000000000^3385 ≤ 61046686215713^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855761137 1250000000 61046686215713 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(246241923/2500000000 : ℝ), (-546848517/1250000000 : ℝ), (855761137/1250000000 : ℝ)] ![(2442817312171/50000000000000 : ℝ), (34067679147423/100000000000000 : ℝ), (61046686215713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(246241923/2500000000 : ℝ)|^4409 ≤ (2442817312171/50000000000000 : ℝ)^3385
        have hw : |(246241923/2500000000 : ℝ)|=(246241923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-546848517/1250000000 : ℝ)|^4409 ≤ (34067679147423/100000000000000 : ℝ)^3385
        have hw : |(-546848517/1250000000 : ℝ)|=(546848517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(855761137/1250000000 : ℝ)|^4409 ≤ (61046686215713/100000000000000 : ℝ)^3385
        have hw : |(855761137/1250000000 : ℝ)|=(855761137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1449_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11381/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (569/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (569/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (569/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (569/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (569/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (569/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (569/5000 : ℝ) ^ (551/128 : ℝ) ≤ (864942811663039/10000000000000000000 : ℝ) := by
    have hpowers : (569/5000 : ℝ)^551 ≤ (864942811663039/10000000000000000000 : ℝ)^128 := by
      have hnat : (569 : ℕ)^551*10000000000000000000^128 ≤ 864942811663039^128*5000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        569 5000 864942811663039 10000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (569/5000 : ℝ)) (X := (864942811663039/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14767/100000 : ℝ) ^ (551/128 : ℝ) ≤ (26549896935295707/100000000000000000000 : ℝ) := by
    have hpowers : (14767/100000 : ℝ)^551 ≤ (26549896935295707/100000000000000000000 : ℝ)^128 := by
      have hnat : (14767 : ℕ)^551*100000000000000000000^128 ≤ 26549896935295707^128*100000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14767 100000 26549896935295707 100000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14767/100000 : ℝ)) (X := (26549896935295707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000864942811663039/5000000000000000000 : ℝ) ≤ (10000401834225711/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (5000864942811663039/5000000000000000000 : ℝ)^128 ≤ (10000401834225711/10000000000000000 : ℝ)^551 := by
      have hnat : (5000864942811663039 : ℕ)^128*10000000000000000^551 ≤ 10000401834225711^551*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000864942811663039 5000000000000000000 10000401834225711 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000401834225711/10000000000000000 : ℝ)) (X := (5000864942811663039/5000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035199325051926097/100000000000000000000 : ℝ) ≤ (10000817587111627/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (100035199325051926097/100000000000000000000 : ℝ)^128 ≤ (10000817587111627/10000000000000000 : ℝ)^551 := by
      have hnat : (100035199325051926097 : ℕ)^128*10000000000000000^551 ≤ 10000817587111627^551*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035199325051926097 100000000000000000000 10000817587111627 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000817587111627/10000000000000000 : ℝ)) (X := (100035199325051926097/100000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026549896935295707/50000000000000000000 : ℝ) ≤ (10001233339997543/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (50026549896935295707/50000000000000000000 : ℝ)^128 ≤ (10001233339997543/10000000000000000 : ℝ)^551 := by
      have hnat : (50026549896935295707 : ℕ)^128*10000000000000000^551 ≤ 10001233339997543^551*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026549896935295707 50000000000000000000 10001233339997543 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001233339997543/10000000000000000 : ℝ)) (X := (50026549896935295707/50000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(864942811663039/10000000000000000000 : ℝ) ≤ ((33861898476839034997/33870000000000000000 : ℝ)+2*(103938221479/84675000000000 : ℝ)*(569/5000 : ℝ))^(551/128 : ℝ) := by
    rw [show (33861898476839034997/33870000000000000000 : ℝ)+2*(103938221479/84675000000000 : ℝ)*(569/5000 : ℝ)=(10000401834225711/10000000000000000 : ℝ) by norm_num, show 1+2*(864942811663039/10000000000000000000 : ℝ)=(5000864942811663039/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26549896935295707/100000000000000000000 : ℝ)+(864942811663039/10000000000000000000 : ℝ) ≤ ((33861898476839034997/33870000000000000000 : ℝ)+(103938221479/84675000000000 : ℝ)*((14767/100000 : ℝ)+(569/5000 : ℝ)))^(551/128 : ℝ) := by
    rw [show (33861898476839034997/33870000000000000000 : ℝ)+(103938221479/84675000000000 : ℝ)*((14767/100000 : ℝ)+(569/5000 : ℝ))=(10000817587111627/10000000000000000 : ℝ) by norm_num, show 1+(26549896935295707/100000000000000000000 : ℝ)+(864942811663039/10000000000000000000 : ℝ)=(100035199325051926097/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26549896935295707/100000000000000000000 : ℝ) ≤ ((33861898476839034997/33870000000000000000 : ℝ)+2*(103938221479/84675000000000 : ℝ)*(14767/100000 : ℝ))^(551/128 : ℝ) := by
    rw [show (33861898476839034997/33870000000000000000 : ℝ)+2*(103938221479/84675000000000 : ℝ)*(14767/100000 : ℝ)=(10001233339997543/10000000000000000 : ℝ) by norm_num, show 1+2*(26549896935295707/100000000000000000000 : ℝ)=(50026549896935295707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33861898476839034997/33870000000000000000 : ℝ)*(X 1 0+X 2 0)+(103938221479/84675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (569/5000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (33861898476839034997/33870000000000000000 : ℝ)) (alpha := (103938221479/84675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33861898476839034997/33870000000000000000 : ℝ)*(X 0 1+X 2 1)+(103938221479/84675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (569/5000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (33861898476839034997/33870000000000000000 : ℝ)) (alpha := (103938221479/84675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33861898476839034997/33870000000000000000 : ℝ)*(X 0 2+X 1 2)+(103938221479/84675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (569/5000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (33861898476839034997/33870000000000000000 : ℝ)) (alpha := (103938221479/84675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-3128037/16000000 : ℝ)*X 0 0+(5407167799/10000000000 : ℝ)*X 0 1+(655919073/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336723943/2500000000 : ℝ)*X 1 0+(-81454931/400000000 : ℝ)*X 1 1+(5247349579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534689341/1000000000 : ℝ)*X 2 0+(5247353703/10000000000 : ℝ)*X 2 1+(-2036370947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4299396733/10000000000 : ℝ)*X 0 0+(4128410561/10000000000 : ℝ)*X 0 1+(1119169587/2500000000 : ℝ)*X 0 2+(4299396733/10000000000 : ℝ)*X 1 0+(4128410561/10000000000 : ℝ)*X 1 1+(1119169587/2500000000 : ℝ)*X 1 2+(4299396733/10000000000 : ℝ)*X 2 0+(4128410561/10000000000 : ℝ)*X 2 1+(1119169587/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5305265897/10000000000 : ℝ)*X 1 0+(-1877136107/10000000000 : ℝ)*X 1 1+(5406588471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s7_4 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((-803707/312500000 : ℝ)*X 0 0+(2935738389/5000000000 : ℝ)*X 0 1+(587137709/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s7_5 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((246241923/2500000000 : ℝ)*X 1 0+(-546848517/1250000000 : ℝ)*X 1 1+(855761137/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s7_6 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (415797130759930374893/282250000000000000000000000 : ℝ) := by norm_num
    linear_combination (36889349/20000000000000 : ℝ)*(upper2) + (6612053/3125000000000 : ℝ)*(lower3) + (16111831/50000000000000 : ℝ)*(lower4) + (288625901/100000000000000 : ℝ)*(lower5) + (912861521672083/20000000000000 : ℝ)*(major0) + (912861521672083/20000000000000 : ℝ)*(major1) + (912861521672083/20000000000000 : ℝ)*(major2) + (6257245181896427/100000000000000 : ℝ)*(sp0) + (19553508983731/312500000000 : ℝ)*(sp1) + (6257256243919533/100000000000000 : ℝ)*(sp2) + (1435679461848111/50000000000000 : ℝ)*(sp3) + (32933698779/25000000000000 : ℝ)*(sp4) + (11062023107/100000000000000 : ℝ)*(sp5) + (1634330497/100000000000000 : ℝ)*(sp6) + (1435679461848111/50000000000000 : ℝ)*(f.failure) + (6257256243919533/100000000000000 : ℝ)*(f.sum) + (65191001507407/3387000000000000000000000000 : ℝ)*base65 + (4495338459283711249/677400000000000000000000000000000 : ℝ)*base68 + (8012531932038088751/677400000000000000000000000000000 : ℝ)*base69 + (1865838964213111249/677400000000000000000000000000000 : ℝ)*base72 + (6571008482089/1693500000000000000000000000 : ℝ)*base74 + (8974987250916088751/677400000000000000000000000000000 : ℝ)*base75 + (23498449366483288751/677400000000000000000000000000000 : ℝ)*base77 + (731783504755711249/677400000000000000000000000000000 : ℝ)*base80 + (15379510481593/3387000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1279231/2500000000000000000000 : ℝ)*base89 + (1279231/2500000000000000000000 : ℝ)*base91 + (1279231/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1449_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1449_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1449_box_0 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1795786139/10000000000 : ℝ)*x 0 + (168293727/312500000 : ℝ)*x 1 + (5385398399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1795786139/10000000000 : ℝ)^4409 ≤ (10682142681823/100000000000000 : ℝ)^3385 := by
    have hnat : (1795786139 : ℕ)^4409*100000000000000^3385 ≤ 10682142681823^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795786139 10000000000 10682142681823 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168293727/312500000 : ℝ)^4409 ≤ (8931786665027/20000000000000 : ℝ)^3385 := by
    have hnat : (168293727 : ℕ)^4409*20000000000000^3385 ≤ 8931786665027^3385*312500000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168293727 312500000 8931786665027 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385398399/10000000000 : ℝ)^4409 ≤ (446589239821/1000000000000 : ℝ)^3385 := by
    have hnat : (5385398399 : ℕ)^4409*1000000000000^3385 ≤ 446589239821^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385398399 10000000000 446589239821 1000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1795786139/10000000000 : ℝ), (168293727/312500000 : ℝ), (5385398399/10000000000 : ℝ)] ![(10682142681823/100000000000000 : ℝ), (8931786665027/20000000000000 : ℝ), (446589239821/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1795786139/10000000000 : ℝ)|^4409 ≤ (10682142681823/100000000000000 : ℝ)^3385
        have hw : |(-1795786139/10000000000 : ℝ)|=(1795786139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168293727/312500000 : ℝ)|^4409 ≤ (8931786665027/20000000000000 : ℝ)^3385
        have hw : |(168293727/312500000 : ℝ)|=(168293727/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385398399/10000000000 : ℝ)|^4409 ≤ (446589239821/1000000000000 : ℝ)^3385
        have hw : |(5385398399/10000000000 : ℝ)|=(5385398399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_1 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321548583/2500000000 : ℝ)*x 0 + (-193215973/1000000000 : ℝ)*x 1 + (538539771/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321548583/2500000000 : ℝ)^4409 ≤ (5448799981857/12500000000000 : ℝ)^3385 := by
    have hnat : (1321548583 : ℕ)^4409*12500000000000^3385 ≤ 5448799981857^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321548583 2500000000 5448799981857 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193215973/1000000000 : ℝ)^4409 ≤ (5875341797143/50000000000000 : ℝ)^3385 := by
    have hnat : (193215973 : ℕ)^4409*50000000000000^3385 ≤ 5875341797143^3385*1000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193215973 1000000000 5875341797143 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538539771/1000000000 : ℝ)^4409 ≤ (44658916540077/100000000000000 : ℝ)^3385 := by
    have hnat : (538539771 : ℕ)^4409*100000000000000^3385 ≤ 44658916540077^3385*1000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538539771 1000000000 44658916540077 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321548583/2500000000 : ℝ), (-193215973/1000000000 : ℝ), (538539771/1000000000 : ℝ)] ![(5448799981857/12500000000000 : ℝ), (5875341797143/50000000000000 : ℝ), (44658916540077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321548583/2500000000 : ℝ)|^4409 ≤ (5448799981857/12500000000000 : ℝ)^3385
        have hw : |(1321548583/2500000000 : ℝ)|=(1321548583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-193215973/1000000000 : ℝ)|^4409 ≤ (5875341797143/50000000000000 : ℝ)^3385
        have hw : |(-193215973/1000000000 : ℝ)|=(193215973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538539771/1000000000 : ℝ)|^4409 ≤ (44658916540077/100000000000000 : ℝ)^3385
        have hw : |(538539771/1000000000 : ℝ)|=(538539771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_2 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528619331/1000000000 : ℝ)*x 0 + (5385398829/10000000000 : ℝ)*x 1 + (-1932159589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528619331/1000000000 : ℝ)^4409 ≤ (10897597219487/25000000000000 : ℝ)^3385 := by
    have hnat : (528619331 : ℕ)^4409*25000000000000^3385 ≤ 10897597219487^3385*1000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528619331 1000000000 10897597219487 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385398829/10000000000 : ℝ)^4409 ≤ (8931785725323/20000000000000 : ℝ)^3385 := by
    have hnat : (5385398829 : ℕ)^4409*20000000000000^3385 ≤ 8931785725323^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385398829 10000000000 8931785725323 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1932159589/10000000000 : ℝ)^4409 ≤ (1175068247737/10000000000000 : ℝ)^3385 := by
    have hnat : (1932159589 : ℕ)^4409*10000000000000^3385 ≤ 1175068247737^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932159589 10000000000 1175068247737 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528619331/1000000000 : ℝ), (5385398829/10000000000 : ℝ), (-1932159589/10000000000 : ℝ)] ![(10897597219487/25000000000000 : ℝ), (8931785725323/20000000000000 : ℝ), (1175068247737/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528619331/1000000000 : ℝ)|^4409 ≤ (10897597219487/25000000000000 : ℝ)^3385
        have hw : |(528619331/1000000000 : ℝ)|=(528619331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385398829/10000000000 : ℝ)|^4409 ≤ (8931785725323/20000000000000 : ℝ)^3385
        have hw : |(5385398829/10000000000 : ℝ)|=(5385398829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1932159589/10000000000 : ℝ)|^4409 ≤ (1175068247737/10000000000000 : ℝ)^3385
        have hw : |(-1932159589/10000000000 : ℝ)|=(1932159589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_3 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1111326243/2500000000 : ℝ)*x 0 + (2115058231/5000000000 : ℝ)*x 1 + (2115057781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1111326243/2500000000 : ℝ)^4409 ≤ (34784669626297/100000000000000 : ℝ)^3385 := by
    have hnat : (1111326243 : ℕ)^4409*100000000000000^3385 ≤ 34784669626297^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111326243 2500000000 34784669626297 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115058231/5000000000 : ℝ)^4409 ≤ (32607669697539/100000000000000 : ℝ)^3385 := by
    have hnat : (2115058231 : ℕ)^4409*100000000000000^3385 ≤ 32607669697539^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115058231 5000000000 32607669697539 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115057781/5000000000 : ℝ)^4409 ≤ (4075957582653/12500000000000 : ℝ)^3385 := by
    have hnat : (2115057781 : ℕ)^4409*12500000000000^3385 ≤ 4075957582653^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115057781 5000000000 4075957582653 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1111326243/2500000000 : ℝ), (2115058231/5000000000 : ℝ), (2115057781/5000000000 : ℝ)] ![(34784669626297/100000000000000 : ℝ), (32607669697539/100000000000000 : ℝ), (4075957582653/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1111326243/2500000000 : ℝ)|^4409 ≤ (34784669626297/100000000000000 : ℝ)^3385
        have hw : |(1111326243/2500000000 : ℝ)|=(1111326243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115058231/5000000000 : ℝ)|^4409 ≤ (32607669697539/100000000000000 : ℝ)^3385
        have hw : |(2115058231/5000000000 : ℝ)|=(2115058231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115057781/5000000000 : ℝ)|^4409 ≤ (4075957582653/12500000000000 : ℝ)^3385
        have hw : |(2115057781/5000000000 : ℝ)|=(2115057781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_4 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-529245313/2500000000 : ℝ)*x 0 + (526680591/1000000000 : ℝ)*x 1 + (5266805843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529245313/2500000000 : ℝ)^4409 ≤ (13235456899739/100000000000000 : ℝ)^3385 := by
    have hnat : (529245313 : ℕ)^4409*100000000000000^3385 ≤ 13235456899739^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529245313 2500000000 13235456899739 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526680591/1000000000 : ℝ)^4409 ≤ (21691135950947/50000000000000 : ℝ)^3385 := by
    have hnat : (526680591 : ℕ)^4409*50000000000000^3385 ≤ 21691135950947^3385*1000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526680591 1000000000 21691135950947 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266805843/10000000000 : ℝ)^4409 ≤ (1355695974471/3125000000000 : ℝ)^3385 := by
    have hnat : (5266805843 : ℕ)^4409*3125000000000^3385 ≤ 1355695974471^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266805843 10000000000 1355695974471 3125000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529245313/2500000000 : ℝ), (526680591/1000000000 : ℝ), (5266805843/10000000000 : ℝ)] ![(13235456899739/100000000000000 : ℝ), (21691135950947/50000000000000 : ℝ), (1355695974471/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529245313/2500000000 : ℝ)|^4409 ≤ (13235456899739/100000000000000 : ℝ)^3385
        have hw : |(-529245313/2500000000 : ℝ)|=(529245313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526680591/1000000000 : ℝ)|^4409 ≤ (21691135950947/50000000000000 : ℝ)^3385
        have hw : |(526680591/1000000000 : ℝ)|=(526680591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266805843/10000000000 : ℝ)|^4409 ≤ (1355695974471/3125000000000 : ℝ)^3385
        have hw : |(5266805843/10000000000 : ℝ)|=(5266805843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_5 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684561621/5000000000 : ℝ)*x 0 + (-990216727/5000000000 : ℝ)*x 1 + (5266805851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684561621/5000000000 : ℝ)^4409 ≤ (44483213234709/100000000000000 : ℝ)^3385 := by
    have hnat : (2684561621 : ℕ)^4409*100000000000000^3385 ≤ 44483213234709^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684561621 5000000000 44483213234709 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (990216727/5000000000 : ℝ)^4409 ≤ (3033628870179/25000000000000 : ℝ)^3385 := by
    have hnat : (990216727 : ℕ)^4409*25000000000000^3385 ≤ 3033628870179^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990216727 5000000000 3033628870179 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266805851/10000000000 : ℝ)^4409 ≤ (21691135634451/50000000000000 : ℝ)^3385 := by
    have hnat : (5266805851 : ℕ)^4409*50000000000000^3385 ≤ 21691135634451^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266805851 10000000000 21691135634451 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684561621/5000000000 : ℝ), (-990216727/5000000000 : ℝ), (5266805851/10000000000 : ℝ)] ![(44483213234709/100000000000000 : ℝ), (3033628870179/25000000000000 : ℝ), (21691135634451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684561621/5000000000 : ℝ)|^4409 ≤ (44483213234709/100000000000000 : ℝ)^3385
        have hw : |(2684561621/5000000000 : ℝ)|=(2684561621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-990216727/5000000000 : ℝ)|^4409 ≤ (3033628870179/25000000000000 : ℝ)^3385
        have hw : |(-990216727/5000000000 : ℝ)|=(990216727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266805851/10000000000 : ℝ)|^4409 ≤ (21691135634451/50000000000000 : ℝ)^3385
        have hw : |(5266805851/10000000000 : ℝ)|=(5266805851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_6 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073824683/2000000000 : ℝ)*x 0 + (2633402883/5000000000 : ℝ)*x 1 + (-396086667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073824683/2000000000 : ℝ)^4409 ≤ (22241607550803/50000000000000 : ℝ)^3385 := by
    have hnat : (1073824683 : ℕ)^4409*50000000000000^3385 ≤ 22241607550803^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073824683 2000000000 22241607550803 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633402883/5000000000 : ℝ)^4409 ≤ (10845567589241/25000000000000 : ℝ)^3385 := by
    have hnat : (2633402883 : ℕ)^4409*25000000000000^3385 ≤ 10845567589241^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633402883 5000000000 10845567589241 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396086667/2000000000 : ℝ)^4409 ≤ (12134514531007/100000000000000 : ℝ)^3385 := by
    have hnat : (396086667 : ℕ)^4409*100000000000000^3385 ≤ 12134514531007^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396086667 2000000000 12134514531007 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073824683/2000000000 : ℝ), (2633402883/5000000000 : ℝ), (-396086667/2000000000 : ℝ)] ![(22241607550803/50000000000000 : ℝ), (10845567589241/25000000000000 : ℝ), (12134514531007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073824683/2000000000 : ℝ)|^4409 ≤ (22241607550803/50000000000000 : ℝ)^3385
        have hw : |(1073824683/2000000000 : ℝ)|=(1073824683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633402883/5000000000 : ℝ)|^4409 ≤ (10845567589241/25000000000000 : ℝ)^3385
        have hw : |(2633402883/5000000000 : ℝ)|=(2633402883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-396086667/2000000000 : ℝ)|^4409 ≤ (12134514531007/100000000000000 : ℝ)^3385
        have hw : |(-396086667/2000000000 : ℝ)|=(396086667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_7 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2076208801/5000000000 : ℝ)*x 0 + (68382957/156250000 : ℝ)*x 1 + (4376509489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2076208801/5000000000 : ℝ)^4409 ≤ (31829722645503/100000000000000 : ℝ)^3385 := by
    have hnat : (2076208801 : ℕ)^4409*100000000000000^3385 ≤ 31829722645503^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076208801 5000000000 31829722645503 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68382957/156250000 : ℝ)^4409 ≤ (17042568723093/50000000000000 : ℝ)^3385 := by
    have hnat : (68382957 : ℕ)^4409*50000000000000^3385 ≤ 17042568723093^3385*156250000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68382957 156250000 17042568723093 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4376509489/10000000000 : ℝ)^4409 ≤ (34085139890943/100000000000000 : ℝ)^3385 := by
    have hnat : (4376509489 : ℕ)^4409*100000000000000^3385 ≤ 34085139890943^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376509489 10000000000 34085139890943 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2076208801/5000000000 : ℝ), (68382957/156250000 : ℝ), (4376509489/10000000000 : ℝ)] ![(31829722645503/100000000000000 : ℝ), (17042568723093/50000000000000 : ℝ), (34085139890943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2076208801/5000000000 : ℝ)|^4409 ≤ (31829722645503/100000000000000 : ℝ)^3385
        have hw : |(2076208801/5000000000 : ℝ)|=(2076208801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68382957/156250000 : ℝ)|^4409 ≤ (17042568723093/50000000000000 : ℝ)^3385
        have hw : |(68382957/156250000 : ℝ)|=(68382957/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4376509489/10000000000 : ℝ)|^4409 ≤ (34085139890943/100000000000000 : ℝ)^3385
        have hw : |(4376509489/10000000000 : ℝ)|=(4376509489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_8 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049285661/10000000000 : ℝ)*x 0 + (5184687643/10000000000 : ℝ)*x 1 + (2699680203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049285661/10000000000 : ℝ)^4409 ≤ (6343437072513/50000000000000 : ℝ)^3385 := by
    have hnat : (2049285661 : ℕ)^4409*50000000000000^3385 ≤ 6343437072513^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049285661 10000000000 6343437072513 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184687643/10000000000 : ℝ)^4409 ≤ (340026691061/800000000000 : ℝ)^3385 := by
    have hnat : (5184687643 : ℕ)^4409*800000000000^3385 ≤ 340026691061^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184687643 10000000000 340026691061 800000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699680203/5000000000 : ℝ)^4409 ≤ (11202447364203/25000000000000 : ℝ)^3385 := by
    have hnat : (2699680203 : ℕ)^4409*25000000000000^3385 ≤ 11202447364203^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699680203 5000000000 11202447364203 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049285661/10000000000 : ℝ), (5184687643/10000000000 : ℝ), (2699680203/5000000000 : ℝ)] ![(6343437072513/50000000000000 : ℝ), (340026691061/800000000000 : ℝ), (11202447364203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049285661/10000000000 : ℝ)|^4409 ≤ (6343437072513/50000000000000 : ℝ)^3385
        have hw : |(-2049285661/10000000000 : ℝ)|=(2049285661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184687643/10000000000 : ℝ)|^4409 ≤ (340026691061/800000000000 : ℝ)^3385
        have hw : |(5184687643/10000000000 : ℝ)|=(5184687643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699680203/5000000000 : ℝ)|^4409 ≤ (11202447364203/25000000000000 : ℝ)^3385
        have hw : |(2699680203/5000000000 : ℝ)|=(2699680203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_9 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527642671/1000000000 : ℝ)*x 0 + (-1926351389/10000000000 : ℝ)*x 1 + (5399360149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527642671/1000000000 : ℝ)^4409 ≤ (43485518919763/100000000000000 : ℝ)^3385 := by
    have hnat : (527642671 : ℕ)^4409*100000000000000^3385 ≤ 43485518919763^3385*1000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527642671 1000000000 43485518919763 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1926351389/10000000000 : ℝ)^4409 ≤ (11704694380791/100000000000000 : ℝ)^3385 := by
    have hnat : (1926351389 : ℕ)^4409*100000000000000^3385 ≤ 11704694380791^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926351389 10000000000 11704694380791 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399360149/10000000000 : ℝ)^4409 ≤ (44809786678729/100000000000000 : ℝ)^3385 := by
    have hnat : (5399360149 : ℕ)^4409*100000000000000^3385 ≤ 44809786678729^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399360149 10000000000 44809786678729 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527642671/1000000000 : ℝ), (-1926351389/10000000000 : ℝ), (5399360149/10000000000 : ℝ)] ![(43485518919763/100000000000000 : ℝ), (11704694380791/100000000000000 : ℝ), (44809786678729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527642671/1000000000 : ℝ)|^4409 ≤ (43485518919763/100000000000000 : ℝ)^3385
        have hw : |(527642671/1000000000 : ℝ)|=(527642671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1926351389/10000000000 : ℝ)|^4409 ≤ (11704694380791/100000000000000 : ℝ)^3385
        have hw : |(-1926351389/10000000000 : ℝ)|=(1926351389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399360149/10000000000 : ℝ)|^4409 ≤ (44809786678729/100000000000000 : ℝ)^3385
        have hw : |(5399360149/10000000000 : ℝ)|=(5399360149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_10 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276426459/10000000000 : ℝ)*x 0 + (5399360259/10000000000 : ℝ)*x 1 + (-1926351579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276426459/10000000000 : ℝ)^4409 ≤ (43485516225377/100000000000000 : ℝ)^3385 := by
    have hnat : (5276426459 : ℕ)^4409*100000000000000^3385 ≤ 43485516225377^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276426459 10000000000 43485516225377 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399360259/10000000000 : ℝ)^4409 ≤ (2800611741737/6250000000000 : ℝ)^3385 := by
    have hnat : (5399360259 : ℕ)^4409*6250000000000^3385 ≤ 2800611741737^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399360259 10000000000 2800611741737 6250000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926351579/10000000000 : ℝ)^4409 ≤ (2340939176897/20000000000000 : ℝ)^3385 := by
    have hnat : (1926351579 : ℕ)^4409*20000000000000^3385 ≤ 2340939176897^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926351579 10000000000 2340939176897 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276426459/10000000000 : ℝ), (5399360259/10000000000 : ℝ), (-1926351579/10000000000 : ℝ)] ![(43485516225377/100000000000000 : ℝ), (2800611741737/6250000000000 : ℝ), (2340939176897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276426459/10000000000 : ℝ)|^4409 ≤ (43485516225377/100000000000000 : ℝ)^3385
        have hw : |(5276426459/10000000000 : ℝ)|=(5276426459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399360259/10000000000 : ℝ)|^4409 ≤ (2800611741737/6250000000000 : ℝ)^3385
        have hw : |(5399360259/10000000000 : ℝ)|=(5399360259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1926351579/10000000000 : ℝ)|^4409 ≤ (2340939176897/20000000000000 : ℝ)^3385
        have hw : |(-1926351579/10000000000 : ℝ)|=(1926351579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_11 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4479228949/10000000000 : ℝ)*x 0 + (526608379/1250000000 : ℝ)*x 1 + (4212866987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4479228949/10000000000 : ℝ)^4409 ≤ (35130827836299/100000000000000 : ℝ)^3385 := by
    have hnat : (4479228949 : ℕ)^4409*100000000000000^3385 ≤ 35130827836299^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479228949 10000000000 35130827836299 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526608379/1250000000 : ℝ)^4409 ≤ (1013580821899/3125000000000 : ℝ)^3385 := by
    have hnat : (526608379 : ℕ)^4409*3125000000000^3385 ≤ 1013580821899^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526608379 1250000000 1013580821899 3125000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4212866987/10000000000 : ℝ)^4409 ≤ (3243458584951/10000000000000 : ℝ)^3385 := by
    have hnat : (4212866987 : ℕ)^4409*10000000000000^3385 ≤ 3243458584951^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212866987 10000000000 3243458584951 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4479228949/10000000000 : ℝ), (526608379/1250000000 : ℝ), (4212866987/10000000000 : ℝ)] ![(35130827836299/100000000000000 : ℝ), (1013580821899/3125000000000 : ℝ), (3243458584951/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4479228949/10000000000 : ℝ)|^4409 ≤ (35130827836299/100000000000000 : ℝ)^3385
        have hw : |(4479228949/10000000000 : ℝ)|=(4479228949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526608379/1250000000 : ℝ)|^4409 ≤ (1013580821899/3125000000000 : ℝ)^3385
        have hw : |(526608379/1250000000 : ℝ)|=(526608379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4212866987/10000000000 : ℝ)|^4409 ≤ (3243458584951/10000000000000 : ℝ)^3385
        have hw : |(4212866987/10000000000 : ℝ)|=(4212866987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_12 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1863629197/10000000000 : ℝ)*x 0 + (1366382817/2500000000 : ℝ)*x 1 + (5255670407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1863629197/10000000000 : ℝ)^4409 ≤ (2802690760601/25000000000000 : ℝ)^3385 := by
    have hnat : (1863629197 : ℕ)^4409*25000000000000^3385 ≤ 2802690760601^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863629197 10000000000 2802690760601 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366382817/2500000000 : ℝ)^4409 ≤ (45526396093057/100000000000000 : ℝ)^3385 := by
    have hnat : (1366382817 : ℕ)^4409*100000000000000^3385 ≤ 45526396093057^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366382817 2500000000 45526396093057 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255670407/10000000000 : ℝ)^4409 ≤ (43262840847527/100000000000000 : ℝ)^3385 := by
    have hnat : (5255670407 : ℕ)^4409*100000000000000^3385 ≤ 43262840847527^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255670407 10000000000 43262840847527 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1863629197/10000000000 : ℝ), (1366382817/2500000000 : ℝ), (5255670407/10000000000 : ℝ)] ![(2802690760601/25000000000000 : ℝ), (45526396093057/100000000000000 : ℝ), (43262840847527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1863629197/10000000000 : ℝ)|^4409 ≤ (2802690760601/25000000000000 : ℝ)^3385
        have hw : |(-1863629197/10000000000 : ℝ)|=(1863629197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366382817/2500000000 : ℝ)|^4409 ≤ (45526396093057/100000000000000 : ℝ)^3385
        have hw : |(1366382817/2500000000 : ℝ)|=(1366382817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255670407/10000000000 : ℝ)|^4409 ≤ (43262840847527/100000000000000 : ℝ)^3385
        have hw : |(5255670407/10000000000 : ℝ)|=(5255670407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_13 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376908629/10000000000 : ℝ)*x 0 + (-1984867253/10000000000 : ℝ)*x 1 + (5255670451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376908629/10000000000 : ℝ)^4409 ≤ (22283623093197/50000000000000 : ℝ)^3385 := by
    have hnat : (5376908629 : ℕ)^4409*50000000000000^3385 ≤ 22283623093197^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376908629 10000000000 22283623093197 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1984867253/10000000000 : ℝ)^4409 ≤ (608495624531/5000000000000 : ℝ)^3385 := by
    have hnat : (1984867253 : ℕ)^4409*5000000000000^3385 ≤ 608495624531^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984867253 10000000000 608495624531 5000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255670451/10000000000 : ℝ)^4409 ≤ (21631420659643/50000000000000 : ℝ)^3385 := by
    have hnat : (5255670451 : ℕ)^4409*50000000000000^3385 ≤ 21631420659643^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255670451 10000000000 21631420659643 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376908629/10000000000 : ℝ), (-1984867253/10000000000 : ℝ), (5255670451/10000000000 : ℝ)] ![(22283623093197/50000000000000 : ℝ), (608495624531/5000000000000 : ℝ), (21631420659643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376908629/10000000000 : ℝ)|^4409 ≤ (22283623093197/50000000000000 : ℝ)^3385
        have hw : |(5376908629/10000000000 : ℝ)|=(5376908629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1984867253/10000000000 : ℝ)|^4409 ≤ (608495624531/5000000000000 : ℝ)^3385
        have hw : |(-1984867253/10000000000 : ℝ)|=(1984867253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255670451/10000000000 : ℝ)|^4409 ≤ (21631420659643/50000000000000 : ℝ)^3385
        have hw : |(5255670451/10000000000 : ℝ)|=(5255670451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_14 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075381711/2000000000 : ℝ)*x 0 + (5255670487/10000000000 : ℝ)*x 1 + (-1984867303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075381711/2000000000 : ℝ)^4409 ≤ (44567245387487/100000000000000 : ℝ)^3385 := by
    have hnat : (1075381711 : ℕ)^4409*100000000000000^3385 ≤ 44567245387487^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075381711 2000000000 44567245387487 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255670487/10000000000 : ℝ)^4409 ≤ (5407855213159/12500000000000 : ℝ)^3385 := by
    have hnat : (5255670487 : ℕ)^4409*12500000000000^3385 ≤ 5407855213159^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255670487 10000000000 5407855213159 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984867303/10000000000 : ℝ)^4409 ≤ (1521239111241/12500000000000 : ℝ)^3385 := by
    have hnat : (1984867303 : ℕ)^4409*12500000000000^3385 ≤ 1521239111241^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984867303 10000000000 1521239111241 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075381711/2000000000 : ℝ), (5255670487/10000000000 : ℝ), (-1984867303/10000000000 : ℝ)] ![(44567245387487/100000000000000 : ℝ), (5407855213159/12500000000000 : ℝ), (1521239111241/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075381711/2000000000 : ℝ)|^4409 ≤ (44567245387487/100000000000000 : ℝ)^3385
        have hw : |(1075381711/2000000000 : ℝ)|=(1075381711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255670487/10000000000 : ℝ)|^4409 ≤ (5407855213159/12500000000000 : ℝ)^3385
        have hw : |(5255670487/10000000000 : ℝ)|=(5255670487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984867303/10000000000 : ℝ)|^4409 ≤ (1521239111241/12500000000000 : ℝ)^3385
        have hw : |(-1984867303/10000000000 : ℝ)|=(1984867303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_box_15 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1031116591/2500000000 : ℝ)*x 0 + (1097561017/2500000000 : ℝ)*x 1 + (4390243907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031116591/2500000000 : ℝ)^4409 ≤ (31550936486401/100000000000000 : ℝ)^3385 := by
    have hnat : (1031116591 : ℕ)^4409*100000000000000^3385 ≤ 31550936486401^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031116591 2500000000 31550936486401 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097561017/2500000000 : ℝ)^4409 ≤ (34224532560237/100000000000000 : ℝ)^3385 := by
    have hnat : (1097561017 : ℕ)^4409*100000000000000^3385 ≤ 34224532560237^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097561017 2500000000 34224532560237 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4390243907/10000000000 : ℝ)^4409 ≤ (34224530925469/100000000000000 : ℝ)^3385 := by
    have hnat : (4390243907 : ℕ)^4409*100000000000000^3385 ≤ 34224530925469^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4390243907 10000000000 34224530925469 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1031116591/2500000000 : ℝ), (1097561017/2500000000 : ℝ), (4390243907/10000000000 : ℝ)] ![(31550936486401/100000000000000 : ℝ), (34224532560237/100000000000000 : ℝ), (34224530925469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1031116591/2500000000 : ℝ)|^4409 ≤ (31550936486401/100000000000000 : ℝ)^3385
        have hw : |(1031116591/2500000000 : ℝ)|=(1031116591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097561017/2500000000 : ℝ)|^4409 ≤ (34224532560237/100000000000000 : ℝ)^3385
        have hw : |(1097561017/2500000000 : ℝ)|=(1097561017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4390243907/10000000000 : ℝ)|^4409 ≤ (34224530925469/100000000000000 : ℝ)^3385
        have hw : |(4390243907/10000000000 : ℝ)|=(4390243907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1449_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1966/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59153/100000 : ℝ) ∧ (40279/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84759/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11381/100000 : ℝ) ^ (551/128 : ℝ) ≤ (1730540078362971/20000000000000000000 : ℝ) := by
    have hpowers : (11381/100000 : ℝ)^551 ≤ (1730540078362971/20000000000000000000 : ℝ)^128 := by
      have hnat : (11381 : ℕ)^551*20000000000000000000^128 ≤ 1730540078362971^128*100000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11381 100000 1730540078362971 20000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11381/100000 : ℝ)) (X := (1730540078362971/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14767/100000 : ℝ) ^ (551/128 : ℝ) ≤ (26549896935295707/100000000000000000000 : ℝ) := by
    have hpowers : (14767/100000 : ℝ)^551 ≤ (26549896935295707/100000000000000000000 : ℝ)^128 := by
      have hnat : (14767 : ℕ)^551*100000000000000000000^128 ≤ 26549896935295707^128*100000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14767 100000 26549896935295707 100000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14767/100000 : ℝ)) (X := (26549896935295707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001730540078362971/10000000000000000000 : ℝ) ≤ (1250050248279829/1250000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (10001730540078362971/10000000000000000000 : ℝ)^128 ≤ (1250050248279829/1250000000000000 : ℝ)^551 := by
      have hnat : (10001730540078362971 : ℕ)^128*1250000000000000^551 ≤ 1250050248279829^551*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001730540078362971 10000000000000000000 1250050248279829 1250000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250050248279829/1250000000000000 : ℝ)) (X := (10001730540078362971/10000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017601298663555281/50000000000000000000 : ℝ) ≤ (10000817663107647/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (50017601298663555281/50000000000000000000 : ℝ)^128 ≤ (10000817663107647/10000000000000000 : ℝ)^551 := by
      have hnat : (50017601298663555281 : ℕ)^128*10000000000000000^551 ≤ 10000817663107647^551*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017601298663555281 50000000000000000000 10000817663107647 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000817663107647/10000000000000000 : ℝ)) (X := (50017601298663555281/50000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026549896935295707/50000000000000000000 : ℝ) ≤ (5000616669988331/5000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (50026549896935295707/50000000000000000000 : ℝ)^128 ≤ (5000616669988331/5000000000000000 : ℝ)^551 := by
      have hnat : (50026549896935295707 : ℕ)^128*5000000000000000^551 ≤ 5000616669988331^551*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026549896935295707 50000000000000000000 5000616669988331 5000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000616669988331/5000000000000000 : ℝ)) (X := (50026549896935295707/50000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1730540078362971/20000000000000000000 : ℝ) ≤ ((16925949744255744261/16930000000000000000 : ℝ)+2*(83135373803/67720000000000 : ℝ)*(11381/100000 : ℝ))^(551/128 : ℝ) := by
    rw [show (16925949744255744261/16930000000000000000 : ℝ)+2*(83135373803/67720000000000 : ℝ)*(11381/100000 : ℝ)=(1250050248279829/1250000000000000 : ℝ) by norm_num, show 1+2*(1730540078362971/20000000000000000000 : ℝ)=(10001730540078362971/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26549896935295707/100000000000000000000 : ℝ)+(1730540078362971/20000000000000000000 : ℝ) ≤ ((16925949744255744261/16930000000000000000 : ℝ)+(83135373803/67720000000000 : ℝ)*((14767/100000 : ℝ)+(11381/100000 : ℝ)))^(551/128 : ℝ) := by
    rw [show (16925949744255744261/16930000000000000000 : ℝ)+(83135373803/67720000000000 : ℝ)*((14767/100000 : ℝ)+(11381/100000 : ℝ))=(10000817663107647/10000000000000000 : ℝ) by norm_num, show 1+(26549896935295707/100000000000000000000 : ℝ)+(1730540078362971/20000000000000000000 : ℝ)=(50017601298663555281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26549896935295707/100000000000000000000 : ℝ) ≤ ((16925949744255744261/16930000000000000000 : ℝ)+2*(83135373803/67720000000000 : ℝ)*(14767/100000 : ℝ))^(551/128 : ℝ) := by
    rw [show (16925949744255744261/16930000000000000000 : ℝ)+2*(83135373803/67720000000000 : ℝ)*(14767/100000 : ℝ)=(5000616669988331/5000000000000000 : ℝ) by norm_num, show 1+2*(26549896935295707/100000000000000000000 : ℝ)=(50026549896935295707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16925949744255744261/16930000000000000000 : ℝ)*(X 1 0+X 2 0)+(83135373803/67720000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (16925949744255744261/16930000000000000000 : ℝ)) (alpha := (83135373803/67720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16925949744255744261/16930000000000000000 : ℝ)*(X 0 1+X 2 1)+(83135373803/67720000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (16925949744255744261/16930000000000000000 : ℝ)) (alpha := (83135373803/67720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16925949744255744261/16930000000000000000 : ℝ)*(X 0 2+X 1 2)+(83135373803/67720000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (16925949744255744261/16930000000000000000 : ℝ)) (alpha := (83135373803/67720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1795786139/10000000000 : ℝ)*X 0 0+(168293727/312500000 : ℝ)*X 0 1+(5385398399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321548583/2500000000 : ℝ)*X 1 0+(-193215973/1000000000 : ℝ)*X 1 1+(538539771/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((528619331/1000000000 : ℝ)*X 2 0+(5385398829/10000000000 : ℝ)*X 2 1+(-1932159589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1111326243/2500000000 : ℝ)*X 0 0+(2115058231/5000000000 : ℝ)*X 0 1+(2115057781/5000000000 : ℝ)*X 0 2+(1111326243/2500000000 : ℝ)*X 1 0+(2115058231/5000000000 : ℝ)*X 1 1+(2115057781/5000000000 : ℝ)*X 1 2+(1111326243/2500000000 : ℝ)*X 2 0+(2115058231/5000000000 : ℝ)*X 2 1+(2115057781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-529245313/2500000000 : ℝ)*X 0 0+(526680591/1000000000 : ℝ)*X 0 1+(5266805843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2684561621/5000000000 : ℝ)*X 1 0+(-990216727/5000000000 : ℝ)*X 1 1+(5266805851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1073824683/2000000000 : ℝ)*X 2 0+(2633402883/5000000000 : ℝ)*X 2 1+(-396086667/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2076208801/5000000000 : ℝ)*X 0 0+(68382957/156250000 : ℝ)*X 0 1+(4376509489/10000000000 : ℝ)*X 0 2+(2076208801/5000000000 : ℝ)*X 1 0+(68382957/156250000 : ℝ)*X 1 1+(4376509489/10000000000 : ℝ)*X 1 2+(2076208801/5000000000 : ℝ)*X 2 0+(68382957/156250000 : ℝ)*X 2 1+(4376509489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2049285661/10000000000 : ℝ)*X 0 0+(5184687643/10000000000 : ℝ)*X 0 1+(2699680203/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((527642671/1000000000 : ℝ)*X 1 0+(-1926351389/10000000000 : ℝ)*X 1 1+(5399360149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276426459/10000000000 : ℝ)*X 2 0+(5399360259/10000000000 : ℝ)*X 2 1+(-1926351579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4479228949/10000000000 : ℝ)*X 0 0+(526608379/1250000000 : ℝ)*X 0 1+(4212866987/10000000000 : ℝ)*X 0 2+(4479228949/10000000000 : ℝ)*X 1 0+(526608379/1250000000 : ℝ)*X 1 1+(4212866987/10000000000 : ℝ)*X 1 2+(4479228949/10000000000 : ℝ)*X 2 0+(526608379/1250000000 : ℝ)*X 2 1+(4212866987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1863629197/10000000000 : ℝ)*X 0 0+(1366382817/2500000000 : ℝ)*X 0 1+(5255670407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5376908629/10000000000 : ℝ)*X 1 0+(-1984867253/10000000000 : ℝ)*X 1 1+(5255670451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1075381711/2000000000 : ℝ)*X 2 0+(5255670487/10000000000 : ℝ)*X 2 1+(-1984867303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1031116591/2500000000 : ℝ)*X 0 0+(1097561017/2500000000 : ℝ)*X 0 1+(4390243907/10000000000 : ℝ)*X 0 2+(1031116591/2500000000 : ℝ)*X 1 0+(1097561017/2500000000 : ℝ)*X 1 1+(4390243907/10000000000 : ℝ)*X 1 2+(1031116591/2500000000 : ℝ)*X 2 0+(1097561017/2500000000 : ℝ)*X 2 1+(4390243907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1966/3125 : ℝ) ≤ (-53253094244768892876614759849367/84650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9666631/25000000000000 : ℝ)*(upper0) + (2783781/6250000000000 : ℝ)*(lower1) + (10069641/12500000000000 : ℝ)*(lower2) + (3972261/50000000000000 : ℝ)*(lower3) + (303848387723683/10000000000000 : ℝ)*(major0) + (303848387723683/10000000000000 : ℝ)*(major1) + (303848387723683/10000000000000 : ℝ)*(major2) + (700866131/25000000000000 : ℝ)*(sp1) + (455728193/25000000000000 : ℝ)*(sp2) + (4186458743681463/100000000000000 : ℝ)*(sp4) + (4186455940216939/100000000000000 : ℝ)*(sp5) + (4186456920768691/100000000000000 : ℝ)*(sp6) + (38229342801659/2000000000000 : ℝ)*(sp7) + (11783780619/100000000000000 : ℝ)*(sp15) + (1911478923863569/100000000000000 : ℝ)*(f.failure) + (4186458743681463/100000000000000 : ℝ)*(f.sum) + (227495665561/67720000000000000000000000 : ℝ)*base65 + (621080942368683263/169300000000000000000000000000000 : ℝ)*base67 + (641455643757683263/169300000000000000000000000000000 : ℝ)*base69 + (892761155748683263/169300000000000000000000000000000 : ℝ)*base71 + (3891135017107/1693000000000000000000000000 : ℝ)*base73 + (727601947631683263/169300000000000000000000000000000 : ℝ)*base75 + (2201775062933983263/169300000000000000000000000000000 : ℝ)*base77 + (2293228267463483263/169300000000000000000000000000000 : ℝ)*base79 + (489707368009/67720000000000000000000000 : ℝ)*base82 + (21101951/5000000000000000000000 : ℝ)*base90 + (21101951/5000000000000000000000 : ℝ)*base92 + (21101951/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59153/100000 : ℝ) ≤ (62594380690276655960350888716891/105812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10914779/100000000000000 : ℝ)*(upper2) + (9594759/10000000000000 : ℝ)*(upper3) + (269987559/100000000000000 : ℝ)*(lower5) + (777694020679777/25000000000000 : ℝ)*(major0) + (777694020679777/25000000000000 : ℝ)*(major1) + (777694020679777/25000000000000 : ℝ)*(major2) + (2122435108122311/50000000000000 : ℝ)*(sp0) + (2122296013761657/50000000000000 : ℝ)*(sp1) + (2122429399752119/50000000000000 : ℝ)*(sp2) + (978474796990371/50000000000000 : ℝ)*(sp3) + (17512704861/100000000000000 : ℝ)*(sp6) + (7612053163/100000000000000 : ℝ)*(sp7) + (1523991119/25000000000000 : ℝ)*(sp8) + (56856937157/20000000000000 : ℝ)*(sp9) + (122309825377119/6250000000000 : ℝ)*(f.failure) + (4244876312209099/100000000000000 : ℝ)*(f.sum) + (4501066256273/846500000000000000000000000 : ℝ)*base66 + (3423939117048740203/423250000000000000000000000000000 : ℝ)*base68 + (265313734398009797/423250000000000000000000000000000 : ℝ)*base69 + (3320176604721740203/423250000000000000000000000000000 : ℝ)*base72 + (17533708699737/1693000000000000000000000000 : ℝ)*base74 + (4599900773702740203/423250000000000000000000000000000 : ℝ)*base76 + (4596569300576990203/423250000000000000000000000000000 : ℝ)*base78 + (3521217860932740203/423250000000000000000000000000000 : ℝ)*base80 + (86757508543/42325000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (827599/312500000000000000000 : ℝ)*base89 + (827599/312500000000000000000 : ℝ)*base91 + (827599/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (40279/50000 : ℝ) ≤ (340972255673156372185340255913033/423250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11606779/12500000000000 : ℝ)*(upper2) + (10430309/50000000000000 : ℝ)*(lower3) + (1066873/800000000000 : ℝ)*(lower5) + (3417521098803249/100000000000000 : ℝ)*(major0) + (3417521098803249/100000000000000 : ℝ)*(major1) + (3417521098803249/100000000000000 : ℝ)*(major2) + (242862997/20000000000000 : ℝ)*(sp0) + (24642669177/100000000000000 : ℝ)*(sp2) + (51251153857/100000000000000 : ℝ)*(sp3) + (4658253388695817/100000000000000 : ℝ)*(sp8) + (29114133530489/625000000000 : ℝ)*(sp9) + (2329118361104531/50000000000000 : ℝ)*(sp10) + (537469021586291/25000000000000 : ℝ)*(sp11) + (6761867437/100000000000000 : ℝ)*(sp12) + (107496366874951/5000000000000 : ℝ)*(f.failure) + (29114133530489/625000000000 : ℝ)*(f.sum) + (12554452370267/3386000000000000000000000000 : ℝ)*base66 + (1720666588769653989/1693000000000000000000000000000000 : ℝ)*base67 + (24390133977332653989/1693000000000000000000000000000000 : ℝ)*base69 + (5718904255333346011/1693000000000000000000000000000000 : ℝ)*base72 + (5513157276669/677200000000000000000000000 : ℝ)*base74 + (337530295820653989/1693000000000000000000000000000000 : ℝ)*base75 + (10816310275562653989/1693000000000000000000000000000000 : ℝ)*base77 + (2500665034097653989/1693000000000000000000000000000000 : ℝ)*base79 + (6128256938539/3386000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (141129/250000000000000000000 : ℝ)*base90 + (141129/250000000000000000000 : ℝ)*base92 + (141129/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-84759/100000 : ℝ) ≤ (-71746780573400387242533226709523/84650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23163183/100000000000000 : ℝ)*(lower0) + (43670227/100000000000000 : ℝ)*(upper3) + (10595047/50000000000000 : ℝ)*(lower4) + (345523129860927/10000000000000 : ℝ)*(major0) + (345523129860927/10000000000000 : ℝ)*(major1) + (345523129860927/10000000000000 : ℝ)*(major2) + (859040587/50000000000000 : ℝ)*(sp0) + (10101178567/25000000000000 : ℝ)*(sp5) + (1116566319/5000000000000 : ℝ)*(sp6) + (3406078553/20000000000000 : ℝ)*(sp7) + (1191265692169947/25000000000000 : ℝ)*(sp12) + (4765024082046693/100000000000000 : ℝ)*(sp13) + (4765042155434581/100000000000000 : ℝ)*(sp14) + (2173633405551471/100000000000000 : ℝ)*(sp15) + (543412608986059/25000000000000 : ℝ)*(f.failure) + (4765064486760961/100000000000000 : ℝ)*(f.sum) + (7310095813369/1693000000000000000000000000 : ℝ)*base65 + (179200781401239947/169300000000000000000000000000000 : ℝ)*base67 + (866562750470439947/169300000000000000000000000000000 : ℝ)*base69 + (1339478039272539947/169300000000000000000000000000000 : ℝ)*base71 + (8948047174117/846500000000000000000000000 : ℝ)*base73 + (1437835724268739947/169300000000000000000000000000000 : ℝ)*base75 + (844022029113939947/169300000000000000000000000000000 : ℝ)*base77 + (3177952272846139947/169300000000000000000000000000000 : ℝ)*base79 + (3409775897089/846500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (15578661/1250000000000000000000 : ℝ)*base90 + (15578661/1250000000000000000000 : ℝ)*base92 + (15578661/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1449_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1966/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(59153/100000 : ℝ) else (40279/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84759/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1449_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1449_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1966/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(59153/100000 : ℝ) else (40279/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84759/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1449_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1449_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1449_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1966/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(59153/100000 : ℝ) else (40279/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84759/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1449_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
