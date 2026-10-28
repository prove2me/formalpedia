-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1154_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:37:01.766083+00:00
-- url     : https://prove2.me/submissions/721e0008-a982-46fd-aa92-76daaa2dda05

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
theorem support_rectangle_w1154_s3_0 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157488617/10000000000 : ℝ)*x 0 + (5427954429/10000000000 : ℝ)*x 1 + (5233198081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157488617/10000000000 : ℝ)^8347 ≤ (13103718201097/100000000000000 : ℝ)^6299 := by
    have hnat : (2157488617 : ℕ)^8347*100000000000000^6299 ≤ 13103718201097^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157488617 10000000000 13103718201097 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427954429/10000000000 : ℝ)^8347 ≤ (44499814434803/100000000000000 : ℝ)^6299 := by
    have hnat : (5427954429 : ℕ)^8347*100000000000000^6299 ≤ 44499814434803^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427954429 10000000000 44499814434803 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233198081/10000000000 : ℝ)^8347 ≤ (2119823367551/5000000000000 : ℝ)^6299 := by
    have hnat : (5233198081 : ℕ)^8347*5000000000000^6299 ≤ 2119823367551^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233198081 10000000000 2119823367551 5000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157488617/10000000000 : ℝ), (5427954429/10000000000 : ℝ), (5233198081/10000000000 : ℝ)] ![(13103718201097/100000000000000 : ℝ), (44499814434803/100000000000000 : ℝ), (2119823367551/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157488617/10000000000 : ℝ)|^8347 ≤ (13103718201097/100000000000000 : ℝ)^6299
        have hw : |(-2157488617/10000000000 : ℝ)|=(2157488617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427954429/10000000000 : ℝ)|^8347 ≤ (44499814434803/100000000000000 : ℝ)^6299
        have hw : |(5427954429/10000000000 : ℝ)|=(5427954429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233198081/10000000000 : ℝ)|^8347 ≤ (2119823367551/5000000000000 : ℝ)^6299
        have hw : |(5233198081/10000000000 : ℝ)|=(5233198081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s3_1 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353507317/10000000000 : ℝ)*x 0 + (-2257015553/10000000000 : ℝ)*x 1 + (654149737/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353507317/10000000000 : ℝ)^8347 ≤ (43692846566597/100000000000000 : ℝ)^6299 := by
    have hnat : (5353507317 : ℕ)^8347*100000000000000^6299 ≤ 43692846566597^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353507317 10000000000 43692846566597 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257015553/10000000000 : ℝ)^8347 ≤ (13910688047243/100000000000000 : ℝ)^6299 := by
    have hnat : (2257015553 : ℕ)^8347*100000000000000^6299 ≤ 13910688047243^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257015553 10000000000 13910688047243 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654149737/1250000000 : ℝ)^8347 ≤ (42396465364957/100000000000000 : ℝ)^6299 := by
    have hnat : (654149737 : ℕ)^8347*100000000000000^6299 ≤ 42396465364957^6299*1250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654149737 1250000000 42396465364957 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353507317/10000000000 : ℝ), (-2257015553/10000000000 : ℝ), (654149737/1250000000 : ℝ)] ![(43692846566597/100000000000000 : ℝ), (13910688047243/100000000000000 : ℝ), (42396465364957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353507317/10000000000 : ℝ)|^8347 ≤ (43692846566597/100000000000000 : ℝ)^6299
        have hw : |(5353507317/10000000000 : ℝ)|=(5353507317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2257015553/10000000000 : ℝ)|^8347 ≤ (13910688047243/100000000000000 : ℝ)^6299
        have hw : |(-2257015553/10000000000 : ℝ)|=(2257015553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654149737/1250000000 : ℝ)|^8347 ≤ (42396465364957/100000000000000 : ℝ)^6299
        have hw : |(654149737/1250000000 : ℝ)|=(654149737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s3_2 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353507397/10000000000 : ℝ)*x 0 + (654149743/1250000000 : ℝ)*x 1 + (-451403077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353507397/10000000000 : ℝ)^8347 ≤ (8738569486361/20000000000000 : ℝ)^6299 := by
    have hnat : (5353507397 : ℕ)^8347*20000000000000^6299 ≤ 8738569486361^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353507397 10000000000 8738569486361 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654149743/1250000000 : ℝ)^8347 ≤ (2119823294013/5000000000000 : ℝ)^6299 := by
    have hnat : (654149743 : ℕ)^8347*5000000000000^6299 ≤ 2119823294013^6299*1250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654149743 1250000000 2119823294013 5000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451403077/2000000000 : ℝ)^8347 ≤ (6955343337577/50000000000000 : ℝ)^6299 := by
    have hnat : (451403077 : ℕ)^8347*50000000000000^6299 ≤ 6955343337577^6299*2000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451403077 2000000000 6955343337577 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353507397/10000000000 : ℝ), (654149743/1250000000 : ℝ), (-451403077/2000000000 : ℝ)] ![(8738569486361/20000000000000 : ℝ), (2119823294013/5000000000000 : ℝ), (6955343337577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353507397/10000000000 : ℝ)|^8347 ≤ (8738569486361/20000000000000 : ℝ)^6299
        have hw : |(5353507397/10000000000 : ℝ)|=(5353507397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654149743/1250000000 : ℝ)|^8347 ≤ (2119823294013/5000000000000 : ℝ)^6299
        have hw : |(654149743/1250000000 : ℝ)|=(654149743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-451403077/2000000000 : ℝ)|^8347 ≤ (6955343337577/50000000000000 : ℝ)^6299
        have hw : |(-451403077/2000000000 : ℝ)|=(451403077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s3_3 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180401633/5000000000 : ℝ)*x 0 + (417090043/1000000000 : ℝ)*x 1 + (4559275233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180401633/5000000000 : ℝ)^8347 ≤ (8323738089717/25000000000000 : ℝ)^6299 := by
    have hnat : (2180401633 : ℕ)^8347*25000000000000^6299 ≤ 8323738089717^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180401633 5000000000 8323738089717 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417090043/1000000000 : ℝ)^8347 ≤ (31387359001501/100000000000000 : ℝ)^6299 := by
    have hnat : (417090043 : ℕ)^8347*100000000000000^6299 ≤ 31387359001501^6299*1000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417090043 1000000000 31387359001501 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4559275233/10000000000 : ℝ)^8347 ≤ (8829422154231/25000000000000 : ℝ)^6299 := by
    have hnat : (4559275233 : ℕ)^8347*25000000000000^6299 ≤ 8829422154231^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4559275233 10000000000 8829422154231 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180401633/5000000000 : ℝ), (417090043/1000000000 : ℝ), (4559275233/10000000000 : ℝ)] ![(8323738089717/25000000000000 : ℝ), (31387359001501/100000000000000 : ℝ), (8829422154231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180401633/5000000000 : ℝ)|^8347 ≤ (8323738089717/25000000000000 : ℝ)^6299
        have hw : |(2180401633/5000000000 : ℝ)|=(2180401633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417090043/1000000000 : ℝ)|^8347 ≤ (31387359001501/100000000000000 : ℝ)^6299
        have hw : |(417090043/1000000000 : ℝ)|=(417090043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4559275233/10000000000 : ℝ)|^8347 ≤ (8829422154231/25000000000000 : ℝ)^6299
        have hw : |(4559275233/10000000000 : ℝ)|=(4559275233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s3_4 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-539376521/2500000000 : ℝ)*x 0 + (1046789443/2000000000 : ℝ)*x 1 + (339200073/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539376521/2500000000 : ℝ)^8347 ≤ (6551929390579/50000000000000 : ℝ)^6299 := by
    have hnat : (539376521 : ℕ)^8347*50000000000000^6299 ≤ 6551929390579^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539376521 2500000000 6551929390579 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046789443/2000000000 : ℝ)^8347 ≤ (8480901969639/20000000000000 : ℝ)^6299 := by
    have hnat : (1046789443 : ℕ)^8347*20000000000000^6299 ≤ 8480901969639^6299*2000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046789443 2000000000 8480901969639 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339200073/625000000 : ℝ)^8347 ≤ (44491631360461/100000000000000 : ℝ)^6299 := by
    have hnat : (339200073 : ℕ)^8347*100000000000000^6299 ≤ 44491631360461^6299*625000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339200073 625000000 44491631360461 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-539376521/2500000000 : ℝ), (1046789443/2000000000 : ℝ), (339200073/625000000 : ℝ)] ![(6551929390579/50000000000000 : ℝ), (8480901969639/20000000000000 : ℝ), (44491631360461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-539376521/2500000000 : ℝ)|^8347 ≤ (6551929390579/50000000000000 : ℝ)^6299
        have hw : |(-539376521/2500000000 : ℝ)|=(539376521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046789443/2000000000 : ℝ)|^8347 ≤ (8480901969639/20000000000000 : ℝ)^6299
        have hw : |(1046789443/2000000000 : ℝ)|=(1046789443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339200073/625000000 : ℝ)|^8347 ≤ (44491631360461/100000000000000 : ℝ)^6299
        have hw : |(339200073/625000000 : ℝ)|=(339200073/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s3_5 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652061647/5000000000 : ℝ)*x 0 + (-206301309/1000000000 : ℝ)*x 1 + (5427200809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652061647/5000000000 : ℝ)^8347 ≤ (10789888941077/25000000000000 : ℝ)^6299 := by
    have hnat : (2652061647 : ℕ)^8347*25000000000000^6299 ≤ 10789888941077^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652061647 5000000000 10789888941077 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206301309/1000000000 : ℝ)^8347 ≤ (6174408381757/50000000000000 : ℝ)^6299 := by
    have hnat : (206301309 : ℕ)^8347*50000000000000^6299 ≤ 6174408381757^6299*1000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206301309 1000000000 6174408381757 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427200809/10000000000 : ℝ)^8347 ≤ (22245813730271/50000000000000 : ℝ)^6299 := by
    have hnat : (5427200809 : ℕ)^8347*50000000000000^6299 ≤ 22245813730271^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427200809 10000000000 22245813730271 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652061647/5000000000 : ℝ), (-206301309/1000000000 : ℝ), (5427200809/10000000000 : ℝ)] ![(10789888941077/25000000000000 : ℝ), (6174408381757/50000000000000 : ℝ), (22245813730271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652061647/5000000000 : ℝ)|^8347 ≤ (10789888941077/25000000000000 : ℝ)^6299
        have hw : |(2652061647/5000000000 : ℝ)|=(2652061647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-206301309/1000000000 : ℝ)|^8347 ≤ (6174408381757/50000000000000 : ℝ)^6299
        have hw : |(-206301309/1000000000 : ℝ)|=(206301309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427200809/10000000000 : ℝ)|^8347 ≤ (22245813730271/50000000000000 : ℝ)^6299
        have hw : |(5427200809/10000000000 : ℝ)|=(5427200809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s3_6 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (26520623/50000000 : ℝ)*x 0 + (271359987/500000000 : ℝ)*x 1 + (-2063012779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26520623/50000000 : ℝ)^8347 ≤ (43159569846341/100000000000000 : ℝ)^6299 := by
    have hnat : (26520623 : ℕ)^8347*100000000000000^6299 ≤ 43159569846341^6299*50000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26520623 50000000 43159569846341 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271359987/500000000 : ℝ)^8347 ≤ (4449161584769/10000000000000 : ℝ)^6299 := by
    have hnat : (271359987 : ℕ)^8347*10000000000000^6299 ≤ 4449161584769^6299*500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271359987 500000000 4449161584769 10000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063012779/10000000000 : ℝ)^8347 ≤ (2469762859333/20000000000000 : ℝ)^6299 := by
    have hnat : (2063012779 : ℕ)^8347*20000000000000^6299 ≤ 2469762859333^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063012779 10000000000 2469762859333 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26520623/50000000 : ℝ), (271359987/500000000 : ℝ), (-2063012779/10000000000 : ℝ)] ![(43159569846341/100000000000000 : ℝ), (4449161584769/10000000000000 : ℝ), (2469762859333/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26520623/50000000 : ℝ)|^8347 ≤ (43159569846341/100000000000000 : ℝ)^6299
        have hw : |(26520623/50000000 : ℝ)|=(26520623/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271359987/500000000 : ℝ)|^8347 ≤ (4449161584769/10000000000000 : ℝ)^6299
        have hw : |(271359987/500000000 : ℝ)|=(271359987/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2063012779/10000000000 : ℝ)|^8347 ≤ (2469762859333/20000000000000 : ℝ)^6299
        have hw : |(-2063012779/10000000000 : ℝ)|=(2063012779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s3_7 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180418881/5000000000 : ℝ)*x 0 + (4557781419/10000000000 : ℝ)*x 1 + (4172402949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180418881/5000000000 : ℝ)^8347 ≤ (4161912671323/12500000000000 : ℝ)^6299 := by
    have hnat : (2180418881 : ℕ)^8347*12500000000000^6299 ≤ 4161912671323^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180418881 5000000000 4161912671323 12500000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4557781419/10000000000 : ℝ)^8347 ≤ (35302355563141/100000000000000 : ℝ)^6299 := by
    have hnat : (4557781419 : ℕ)^8347*100000000000000^6299 ≤ 35302355563141^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557781419 10000000000 35302355563141 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172402949/10000000000 : ℝ)^8347 ≤ (31402343049679/100000000000000 : ℝ)^6299 := by
    have hnat : (4172402949 : ℕ)^8347*100000000000000^6299 ≤ 31402343049679^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172402949 10000000000 31402343049679 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180418881/5000000000 : ℝ), (4557781419/10000000000 : ℝ), (4172402949/10000000000 : ℝ)] ![(4161912671323/12500000000000 : ℝ), (35302355563141/100000000000000 : ℝ), (31402343049679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180418881/5000000000 : ℝ)|^8347 ≤ (4161912671323/12500000000000 : ℝ)^6299
        have hw : |(2180418881/5000000000 : ℝ)|=(2180418881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4557781419/10000000000 : ℝ)|^8347 ≤ (35302355563141/100000000000000 : ℝ)^6299
        have hw : |(4557781419/10000000000 : ℝ)|=(4557781419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172402949/10000000000 : ℝ)|^8347 ≤ (31402343049679/100000000000000 : ℝ)^6299
        have hw : |(4172402949/10000000000 : ℝ)|=(4172402949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1154_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16467/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1067/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1849/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16467/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2281/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16467/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2281/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16467/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2281/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16467/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2281/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16467/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2281/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16467/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2281/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2281/25000 : ℝ) ^ (4173/1024 : ℝ) ≤ (231532469897899/4000000000000000000 : ℝ) := by
    have hpowers : (2281/25000 : ℝ)^4173 ≤ (231532469897899/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2281 : ℕ)^4173*4000000000000000000^1024 ≤ 231532469897899^1024*25000^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2281 25000 231532469897899 4000000000000000000 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2281/25000 : ℝ)) (X := (231532469897899/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16467/100000 : ℝ) ^ (4173/1024 : ℝ) ≤ (32101182286929949/50000000000000000000 : ℝ) := by
    have hpowers : (16467/100000 : ℝ)^4173 ≤ (32101182286929949/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16467 : ℕ)^4173*50000000000000000000^1024 ≤ 32101182286929949^1024*100000^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16467 100000 32101182286929949 50000000000000000000 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16467/100000 : ℝ)) (X := (32101182286929949/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000231532469897899/2000000000000000000 : ℝ) ≤ (10000284062897163/10000000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (2000231532469897899/2000000000000000000 : ℝ)^1024 ≤ (10000284062897163/10000000000000000 : ℝ)^4173 := by
      have hnat : (2000231532469897899 : ℕ)^1024*10000000000000000^4173 ≤ 10000284062897163^4173*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000231532469897899 2000000000000000000 10000284062897163 10000000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000284062897163/10000000000000000 : ℝ)) (X := (2000231532469897899/2000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100069990676321307373/100000000000000000000 : ℝ) ≤ (78138414272857/78125000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (100069990676321307373/100000000000000000000 : ℝ)^1024 ≤ (78138414272857/78125000000000 : ℝ)^4173 := by
      have hnat : (100069990676321307373 : ℕ)^1024*78125000000000^4173 ≤ 78138414272857^4173*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100069990676321307373 100000000000000000000 78138414272857 78125000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78138414272857/78125000000000 : ℝ)) (X := (100069990676321307373/100000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25032101182286929949/25000000000000000000 : ℝ) ≤ (10003149990954229/10000000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (25032101182286929949/25000000000000000000 : ℝ)^1024 ≤ (10003149990954229/10000000000000000 : ℝ)^4173 := by
      have hnat : (25032101182286929949 : ℕ)^1024*10000000000000000^4173 ≤ 10003149990954229^4173*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25032101182286929949 25000000000000000000 10003149990954229 10000000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003149990954229/10000000000000000 : ℝ)) (X := (25032101182286929949/25000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(231532469897899/4000000000000000000 : ℝ) ≤ ((2936237485850447909/2937200000000000000 : ℝ)+2*(1432964028533/734300000000000 : ℝ)*(2281/25000 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (2936237485850447909/2937200000000000000 : ℝ)+2*(1432964028533/734300000000000 : ℝ)*(2281/25000 : ℝ)=(10000284062897163/10000000000000000 : ℝ) by norm_num, show 1+2*(231532469897899/4000000000000000000 : ℝ)=(2000231532469897899/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32101182286929949/50000000000000000000 : ℝ)+(231532469897899/4000000000000000000 : ℝ) ≤ ((2936237485850447909/2937200000000000000 : ℝ)+(1432964028533/734300000000000 : ℝ)*((16467/100000 : ℝ)+(2281/25000 : ℝ)))^(4173/1024 : ℝ) := by
    rw [show (2936237485850447909/2937200000000000000 : ℝ)+(1432964028533/734300000000000 : ℝ)*((16467/100000 : ℝ)+(2281/25000 : ℝ))=(78138414272857/78125000000000 : ℝ) by norm_num, show 1+(32101182286929949/50000000000000000000 : ℝ)+(231532469897899/4000000000000000000 : ℝ)=(100069990676321307373/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32101182286929949/50000000000000000000 : ℝ) ≤ ((2936237485850447909/2937200000000000000 : ℝ)+2*(1432964028533/734300000000000 : ℝ)*(16467/100000 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (2936237485850447909/2937200000000000000 : ℝ)+2*(1432964028533/734300000000000 : ℝ)*(16467/100000 : ℝ)=(10003149990954229/10000000000000000 : ℝ) by norm_num, show 1+2*(32101182286929949/50000000000000000000 : ℝ)=(25032101182286929949/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2936237485850447909/2937200000000000000 : ℝ)*(X 1 0+X 2 0)+(1432964028533/734300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (2281/25000 : ℝ)) (hi := (16467/100000 : ℝ)) (c := (2936237485850447909/2937200000000000000 : ℝ)) (alpha := (1432964028533/734300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2936237485850447909/2937200000000000000 : ℝ)*(X 0 1+X 2 1)+(1432964028533/734300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (2281/25000 : ℝ)) (hi := (16467/100000 : ℝ)) (c := (2936237485850447909/2937200000000000000 : ℝ)) (alpha := (1432964028533/734300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2936237485850447909/2937200000000000000 : ℝ)*(X 0 2+X 1 2)+(1432964028533/734300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (2281/25000 : ℝ)) (hi := (16467/100000 : ℝ)) (c := (2936237485850447909/2937200000000000000 : ℝ)) (alpha := (1432964028533/734300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2157488617/10000000000 : ℝ)*X 0 0+(5427954429/10000000000 : ℝ)*X 0 1+(5233198081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353507317/10000000000 : ℝ)*X 1 0+(-2257015553/10000000000 : ℝ)*X 1 1+(654149737/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353507397/10000000000 : ℝ)*X 2 0+(654149743/1250000000 : ℝ)*X 2 1+(-451403077/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180401633/5000000000 : ℝ)*X 0 0+(417090043/1000000000 : ℝ)*X 0 1+(4559275233/10000000000 : ℝ)*X 0 2+(2180401633/5000000000 : ℝ)*X 1 0+(417090043/1000000000 : ℝ)*X 1 1+(4559275233/10000000000 : ℝ)*X 1 2+(2180401633/5000000000 : ℝ)*X 2 0+(417090043/1000000000 : ℝ)*X 2 1+(4559275233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-539376521/2500000000 : ℝ)*X 0 0+(1046789443/2000000000 : ℝ)*X 0 1+(339200073/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652061647/5000000000 : ℝ)*X 1 0+(-206301309/1000000000 : ℝ)*X 1 1+(5427200809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26520623/50000000 : ℝ)*X 2 0+(271359987/500000000 : ℝ)*X 2 1+(-2063012779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180418881/5000000000 : ℝ)*X 0 0+(4557781419/10000000000 : ℝ)*X 0 1+(4172402949/10000000000 : ℝ)*X 0 2+(2180418881/5000000000 : ℝ)*X 1 0+(4557781419/10000000000 : ℝ)*X 1 1+(4172402949/10000000000 : ℝ)*X 1 2+(2180418881/5000000000 : ℝ)*X 2 0+(4557781419/10000000000 : ℝ)*X 2 1+(4172402949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14260171022342571184473249/1835750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1884916283/100000000000000 : ℝ)*(base19) + (1793816337/100000000000000 : ℝ)*(base23) + (89847883/100000000000000 : ℝ)*(lower2) + (35538433/25000000000000 : ℝ)*(upper3) + (104069769/50000000000000 : ℝ)*(upper5) + (48184676405337/1250000000000 : ℝ)*(major0) + (48184676405337/1250000000000 : ℝ)*(major1) + (48184676405337/1250000000000 : ℝ)*(major2) + (1283662574611257/25000000000000 : ℝ)*(sp0) + (5134682503548043/100000000000000 : ℝ)*(sp1) + (5134682594647989/100000000000000 : ℝ)*(sp2) + (2574847898296053/100000000000000 : ℝ)*(sp3) + (17045009649/50000000000000 : ℝ)*(sp4) + (15679159023/100000000000000 : ℝ)*(sp7) + (643715894363769/25000000000000 : ℝ)*(f.failure) + (2567342194232163/50000000000000 : ℝ)*(f.sum) + (570381482387/1835750000000000000000000000 : ℝ)*base65 + (10664383371780833/3671500000000000000000000000000 : ℝ)*base67 + (13980431872047667/3671500000000000000000000000000 : ℝ)*base70 + (13001686144658167/3671500000000000000000000000000 : ℝ)*base72 + (2101889816417/458937500000000000000000000 : ℝ)*base73 + (15021531609338333/3671500000000000000000000000000 : ℝ)*base75 + (31583676348001167/3671500000000000000000000000000 : ℝ)*base78 + (10738811413800167/3671500000000000000000000000000 : ℝ)*base80 + (38399370442963/7343000000000000000000000000 : ℝ)*base81 + (9983793/2500000000000000000000 : ℝ)*base89 + (9983793/2500000000000000000000 : ℝ)*base91 + (9983793/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (182103984593958713044486113/18357500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (404290169/25000000000000 : ℝ)*(base19) + (1519644587/50000000000000 : ℝ)*(base23) + (104725581/100000000000000 : ℝ)*(upper3) + (18417091/100000000000000 : ℝ)*(lower4) + (9877827/5000000000000 : ℝ)*(upper5) + (485587858202973/12500000000000 : ℝ)*(major0) + (485587858202973/12500000000000 : ℝ)*(major1) + (485587858202973/12500000000000 : ℝ)*(major2) + (4628829093/20000000000000 : ℝ)*(sp1) + (35315256861/100000000000000 : ℝ)*(sp2) + (1293637597654061/25000000000000 : ℝ)*(sp4) + (5174525629310103/100000000000000 : ℝ)*(sp5) + (5174512036070209/100000000000000 : ℝ)*(sp6) + (648713752492259/25000000000000 : ℝ)*(sp7) + (648713752492259/25000000000000 : ℝ)*(f.failure) + (1293637597654061/25000000000000 : ℝ)*(f.sum) + (17268361052727/2294687500000000000000000000 : ℝ)*base65 + (345903536803090543/36715000000000000000000000000000 : ℝ)*base68 + (531720267027670543/36715000000000000000000000000000 : ℝ)*base70 + (253023456229215543/36715000000000000000000000000000 : ℝ)*base72 + (247356198526537/36715000000000000000000000000 : ℝ)*base73 + (223051460139795543/36715000000000000000000000000000 : ℝ)*base76 + (478484232713165543/36715000000000000000000000000000 : ℝ)*base78 + (100136226700650543/36715000000000000000000000000000 : ℝ)*base80 + (33342673018813/9178750000000000000000000000 : ℝ)*base81 + (3669323/2500000000000000000000 : ℝ)*base89 + (3669323/2500000000000000000000 : ℝ)*base91 + (3669323/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1154_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16467/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1067/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1154_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1154_s4_0 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160394077/10000000000 : ℝ)*x 0 + (270066421/500000000 : ℝ)*x 1 + (5257923137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160394077/10000000000 : ℝ)^8347 ≤ (6563553684631/50000000000000 : ℝ)^6299 := by
    have hnat : (2160394077 : ℕ)^8347*50000000000000^6299 ≤ 6563553684631^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160394077 10000000000 6563553684631 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270066421/500000000 : ℝ)^8347 ≤ (11052696588123/25000000000000 : ℝ)^6299 := by
    have hnat : (270066421 : ℕ)^8347*25000000000000^6299 ≤ 11052696588123^6299*500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270066421 500000000 11052696588123 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257923137/10000000000 : ℝ)^8347 ≤ (5332763281261/12500000000000 : ℝ)^6299 := by
    have hnat : (5257923137 : ℕ)^8347*12500000000000^6299 ≤ 5332763281261^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257923137 10000000000 5332763281261 12500000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160394077/10000000000 : ℝ), (270066421/500000000 : ℝ), (5257923137/10000000000 : ℝ)] ![(6563553684631/50000000000000 : ℝ), (11052696588123/25000000000000 : ℝ), (5332763281261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160394077/10000000000 : ℝ)|^8347 ≤ (6563553684631/50000000000000 : ℝ)^6299
        have hw : |(-2160394077/10000000000 : ℝ)|=(2160394077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270066421/500000000 : ℝ)|^8347 ≤ (11052696588123/25000000000000 : ℝ)^6299
        have hw : |(270066421/500000000 : ℝ)|=(270066421/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257923137/10000000000 : ℝ)|^8347 ≤ (5332763281261/12500000000000 : ℝ)^6299
        have hw : |(5257923137/10000000000 : ℝ)|=(5257923137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s4_1 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346850323/10000000000 : ℝ)*x 0 + (-558315589/2500000000 : ℝ)*x 1 + (1051584719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346850323/10000000000 : ℝ)^8347 ≤ (1744834601389/4000000000000 : ℝ)^6299 := by
    have hnat : (5346850323 : ℕ)^8347*4000000000000^6299 ≤ 1744834601389^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346850323 10000000000 1744834601389 4000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (558315589/2500000000 : ℝ)^8347 ≤ (13717023774273/100000000000000 : ℝ)^6299 := by
    have hnat : (558315589 : ℕ)^8347*100000000000000^6299 ≤ 13717023774273^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558315589 2500000000 13717023774273 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051584719/2000000000 : ℝ)^8347 ≤ (42662111174477/100000000000000 : ℝ)^6299 := by
    have hnat : (1051584719 : ℕ)^8347*100000000000000^6299 ≤ 42662111174477^6299*2000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051584719 2000000000 42662111174477 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346850323/10000000000 : ℝ), (-558315589/2500000000 : ℝ), (1051584719/2000000000 : ℝ)] ![(1744834601389/4000000000000 : ℝ), (13717023774273/100000000000000 : ℝ), (42662111174477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346850323/10000000000 : ℝ)|^8347 ≤ (1744834601389/4000000000000 : ℝ)^6299
        have hw : |(5346850323/10000000000 : ℝ)|=(5346850323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-558315589/2500000000 : ℝ)|^8347 ≤ (13717023774273/100000000000000 : ℝ)^6299
        have hw : |(-558315589/2500000000 : ℝ)|=(558315589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051584719/2000000000 : ℝ)|^8347 ≤ (42662111174477/100000000000000 : ℝ)^6299
        have hw : |(1051584719/2000000000 : ℝ)|=(1051584719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s4_2 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673425171/5000000000 : ℝ)*x 0 + (657240419/1250000000 : ℝ)*x 1 + (-2233262651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673425171/5000000000 : ℝ)^8347 ≤ (43620865240129/100000000000000 : ℝ)^6299 := by
    have hnat : (2673425171 : ℕ)^8347*100000000000000^6299 ≤ 43620865240129^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673425171 5000000000 43620865240129 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657240419/1250000000 : ℝ)^8347 ≤ (10665527140439/25000000000000 : ℝ)^6299 := by
    have hnat : (657240419 : ℕ)^8347*25000000000000^6299 ≤ 10665527140439^6299*1250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657240419 1250000000 10665527140439 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2233262651/10000000000 : ℝ)^8347 ≤ (6858513087661/50000000000000 : ℝ)^6299 := by
    have hnat : (2233262651 : ℕ)^8347*50000000000000^6299 ≤ 6858513087661^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233262651 10000000000 6858513087661 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673425171/5000000000 : ℝ), (657240419/1250000000 : ℝ), (-2233262651/10000000000 : ℝ)] ![(43620865240129/100000000000000 : ℝ), (10665527140439/25000000000000 : ℝ), (6858513087661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673425171/5000000000 : ℝ)|^8347 ≤ (43620865240129/100000000000000 : ℝ)^6299
        have hw : |(2673425171/5000000000 : ℝ)|=(2673425171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657240419/1250000000 : ℝ)|^8347 ≤ (10665527140439/25000000000000 : ℝ)^6299
        have hw : |(657240419/1250000000 : ℝ)|=(657240419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2233262651/10000000000 : ℝ)|^8347 ≤ (6858513087661/50000000000000 : ℝ)^6299
        have hw : |(-2233262651/10000000000 : ℝ)|=(2233262651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s4_3 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362539029/10000000000 : ℝ)*x 0 + (2110938281/5000000000 : ℝ)*x 1 + (4507849959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362539029/10000000000 : ℝ)^8347 ≤ (33312514976003/100000000000000 : ℝ)^6299 := by
    have hnat : (4362539029 : ℕ)^8347*100000000000000^6299 ≤ 33312514976003^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362539029 10000000000 33312514976003 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110938281/5000000000 : ℝ)^8347 ≤ (15948350978091/50000000000000 : ℝ)^6299 := by
    have hnat : (2110938281 : ℕ)^8347*50000000000000^6299 ≤ 15948350978091^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110938281 5000000000 15948350978091 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507849959/10000000000 : ℝ)^8347 ≤ (8697695762583/25000000000000 : ℝ)^6299 := by
    have hnat : (4507849959 : ℕ)^8347*25000000000000^6299 ≤ 8697695762583^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507849959 10000000000 8697695762583 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362539029/10000000000 : ℝ), (2110938281/5000000000 : ℝ), (4507849959/10000000000 : ℝ)] ![(33312514976003/100000000000000 : ℝ), (15948350978091/50000000000000 : ℝ), (8697695762583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362539029/10000000000 : ℝ)|^8347 ≤ (33312514976003/100000000000000 : ℝ)^6299
        have hw : |(4362539029/10000000000 : ℝ)|=(4362539029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110938281/5000000000 : ℝ)|^8347 ≤ (15948350978091/50000000000000 : ℝ)^6299
        have hw : |(2110938281/5000000000 : ℝ)|=(2110938281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507849959/10000000000 : ℝ)|^8347 ≤ (8697695762583/25000000000000 : ℝ)^6299
        have hw : |(4507849959/10000000000 : ℝ)|=(4507849959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s4_4 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080200561/5000000000 : ℝ)*x 0 + (1051666079/2000000000 : ℝ)*x 1 + (5400919471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080200561/5000000000 : ℝ)^8347 ≤ (13127164094469/100000000000000 : ℝ)^6299 := by
    have hnat : (1080200561 : ℕ)^8347*100000000000000^6299 ≤ 13127164094469^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080200561 5000000000 13127164094469 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051666079/2000000000 : ℝ)^8347 ≤ (1333327659973/3125000000000 : ℝ)^6299 := by
    have hnat : (1051666079 : ℕ)^8347*3125000000000^6299 ≤ 1333327659973^6299*2000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051666079 2000000000 1333327659973 3125000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400919471/10000000000 : ℝ)^8347 ≤ (44206350774041/100000000000000 : ℝ)^6299 := by
    have hnat : (5400919471 : ℕ)^8347*100000000000000^6299 ≤ 44206350774041^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400919471 10000000000 44206350774041 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080200561/5000000000 : ℝ), (1051666079/2000000000 : ℝ), (5400919471/10000000000 : ℝ)] ![(13127164094469/100000000000000 : ℝ), (1333327659973/3125000000000 : ℝ), (44206350774041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080200561/5000000000 : ℝ)|^8347 ≤ (13127164094469/100000000000000 : ℝ)^6299
        have hw : |(-1080200561/5000000000 : ℝ)|=(1080200561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051666079/2000000000 : ℝ)|^8347 ≤ (1333327659973/3125000000000 : ℝ)^6299
        have hw : |(1051666079/2000000000 : ℝ)|=(1051666079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400919471/10000000000 : ℝ)|^8347 ≤ (44206350774041/100000000000000 : ℝ)^6299
        have hw : |(5400919471/10000000000 : ℝ)|=(5400919471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s4_5 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310487851/10000000000 : ℝ)*x 0 + (-2090266519/10000000000 : ℝ)*x 1 + (5400919493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310487851/10000000000 : ℝ)^8347 ≤ (5403524426109/12500000000000 : ℝ)^6299 := by
    have hnat : (5310487851 : ℕ)^8347*12500000000000^6299 ≤ 5403524426109^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310487851 10000000000 5403524426109 12500000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2090266519/10000000000 : ℝ)^8347 ≤ (12565453571551/100000000000000 : ℝ)^6299 := by
    have hnat : (2090266519 : ℕ)^8347*100000000000000^6299 ≤ 12565453571551^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090266519 10000000000 12565453571551 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400919493/10000000000 : ℝ)^8347 ≤ (2762896938291/6250000000000 : ℝ)^6299 := by
    have hnat : (5400919493 : ℕ)^8347*6250000000000^6299 ≤ 2762896938291^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400919493 10000000000 2762896938291 6250000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310487851/10000000000 : ℝ), (-2090266519/10000000000 : ℝ), (5400919493/10000000000 : ℝ)] ![(5403524426109/12500000000000 : ℝ), (12565453571551/100000000000000 : ℝ), (2762896938291/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310487851/10000000000 : ℝ)|^8347 ≤ (5403524426109/12500000000000 : ℝ)^6299
        have hw : |(5310487851/10000000000 : ℝ)|=(5310487851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2090266519/10000000000 : ℝ)|^8347 ≤ (12565453571551/100000000000000 : ℝ)^6299
        have hw : |(-2090266519/10000000000 : ℝ)|=(2090266519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400919493/10000000000 : ℝ)|^8347 ≤ (2762896938291/6250000000000 : ℝ)^6299
        have hw : |(5400919493/10000000000 : ℝ)|=(5400919493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s4_6 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212419513/400000000 : ℝ)*x 0 + (675114979/1250000000 : ℝ)*x 1 + (-522566523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212419513/400000000 : ℝ)^8347 ≤ (1350881097763/3125000000000 : ℝ)^6299 := by
    have hnat : (212419513 : ℕ)^8347*3125000000000^6299 ≤ 1350881097763^6299*400000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212419513 400000000 1350881097763 3125000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675114979/1250000000 : ℝ)^8347 ≤ (44206354689503/100000000000000 : ℝ)^6299 := by
    have hnat : (675114979 : ℕ)^8347*100000000000000^6299 ≤ 44206354689503^6299*1250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675114979 1250000000 44206354689503 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522566523/2500000000 : ℝ)^8347 ≤ (3141362542527/25000000000000 : ℝ)^6299 := by
    have hnat : (522566523 : ℕ)^8347*25000000000000^6299 ≤ 3141362542527^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522566523 2500000000 3141362542527 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212419513/400000000 : ℝ), (675114979/1250000000 : ℝ), (-522566523/2500000000 : ℝ)] ![(1350881097763/3125000000000 : ℝ), (44206354689503/100000000000000 : ℝ), (3141362542527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212419513/400000000 : ℝ)|^8347 ≤ (1350881097763/3125000000000 : ℝ)^6299
        have hw : |(212419513/400000000 : ℝ)|=(212419513/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675114979/1250000000 : ℝ)|^8347 ≤ (44206354689503/100000000000000 : ℝ)^6299
        have hw : |(675114979/1250000000 : ℝ)|=(675114979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522566523/2500000000 : ℝ)|^8347 ≤ (3141362542527/25000000000000 : ℝ)^6299
        have hw : |(-522566523/2500000000 : ℝ)|=(522566523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s4_7 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362552931/10000000000 : ℝ)*x 0 + (1126759539/2500000000 : ℝ)*x 1 + (4222691749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362552931/10000000000 : ℝ)^8347 ≤ (33312655646949/100000000000000 : ℝ)^6299 := by
    have hnat : (4362552931 : ℕ)^8347*100000000000000^6299 ≤ 33312655646949^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362552931 10000000000 33312655646949 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126759539/2500000000 : ℝ)^8347 ≤ (4347810110349/12500000000000 : ℝ)^6299 := by
    have hnat : (1126759539 : ℕ)^8347*12500000000000^6299 ≤ 4347810110349^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126759539 2500000000 4347810110349 12500000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222691749/10000000000 : ℝ)^8347 ≤ (31904863455163/100000000000000 : ℝ)^6299 := by
    have hnat : (4222691749 : ℕ)^8347*100000000000000^6299 ≤ 31904863455163^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222691749 10000000000 31904863455163 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362552931/10000000000 : ℝ), (1126759539/2500000000 : ℝ), (4222691749/10000000000 : ℝ)] ![(33312655646949/100000000000000 : ℝ), (4347810110349/12500000000000 : ℝ), (31904863455163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362552931/10000000000 : ℝ)|^8347 ≤ (33312655646949/100000000000000 : ℝ)^6299
        have hw : |(4362552931/10000000000 : ℝ)|=(4362552931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126759539/2500000000 : ℝ)|^8347 ≤ (4347810110349/12500000000000 : ℝ)^6299
        have hw : |(1126759539/2500000000 : ℝ)|=(1126759539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222691749/10000000000 : ℝ)|^8347 ≤ (31904863455163/100000000000000 : ℝ)^6299
        have hw : |(4222691749/10000000000 : ℝ)|=(4222691749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1154_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1067/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5599/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1849/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1067/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1849/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1067/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1849/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1067/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1849/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1067/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1849/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1067/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1849/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1067/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1067/10000 : ℝ) ^ (4173/1024 : ℝ) ≤ (5477094092463933/50000000000000000000 : ℝ) := by
    have hpowers : (1067/10000 : ℝ)^4173 ≤ (5477094092463933/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1067 : ℕ)^4173*50000000000000000000^1024 ≤ 5477094092463933^1024*10000^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1067 10000 5477094092463933 50000000000000000000 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1067/10000 : ℝ)) (X := (5477094092463933/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1849/12500 : ℝ) ^ (4173/1024 : ℝ) ≤ (10366628002118541/25000000000000000000 : ℝ) := by
    have hpowers : (1849/12500 : ℝ)^4173 ≤ (10366628002118541/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1849 : ℕ)^4173*25000000000000000000^1024 ≤ 10366628002118541^1024*12500^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1849 12500 10366628002118541 25000000000000000000 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1849/12500 : ℝ)) (X := (10366628002118541/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005477094092463933/25000000000000000000 : ℝ) ≤ (2000107511733489/2000000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (25005477094092463933/25000000000000000000 : ℝ)^1024 ≤ (2000107511733489/2000000000000000 : ℝ)^4173 := by
      have hnat : (25005477094092463933 : ℕ)^1024*2000000000000000^4173 ≤ 2000107511733489^4173*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005477094092463933 25000000000000000000 2000107511733489 2000000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000107511733489/2000000000000000 : ℝ)) (X := (25005477094092463933/25000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005242070019340203/10000000000000000000 : ℝ) ≤ (400051443262209/400000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (10005242070019340203/10000000000000000000 : ℝ)^1024 ≤ (400051443262209/400000000000000 : ℝ)^4173 := by
      have hnat : (10005242070019340203 : ℕ)^1024*400000000000000^4173 ≤ 400051443262209^4173*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005242070019340203 10000000000000000000 400051443262209 400000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400051443262209/400000000000000 : ℝ)) (X := (10005242070019340203/10000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12510366628002118541/12500000000000000000 : ℝ) ≤ (2000406920888601/2000000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (12510366628002118541/12500000000000000000 : ℝ)^1024 ≤ (2000406920888601/2000000000000000 : ℝ)^4173 := by
      have hnat : (12510366628002118541 : ℕ)^1024*2000000000000000^4173 ≤ 2000406920888601^4173*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12510366628002118541 12500000000000000000 2000406920888601 2000000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000406920888601/2000000000000000 : ℝ)) (X := (12510366628002118541/12500000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5477094092463933/50000000000000000000 : ℝ) ≤ ((1373541411280066103/1374000000000000000 : ℝ)+2*(12475381463/6870000000000 : ℝ)*(1067/10000 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (1373541411280066103/1374000000000000000 : ℝ)+2*(12475381463/6870000000000 : ℝ)*(1067/10000 : ℝ)=(2000107511733489/2000000000000000 : ℝ) by norm_num, show 1+2*(5477094092463933/50000000000000000000 : ℝ)=(25005477094092463933/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10366628002118541/25000000000000000000 : ℝ)+(5477094092463933/50000000000000000000 : ℝ) ≤ ((1373541411280066103/1374000000000000000 : ℝ)+(12475381463/6870000000000 : ℝ)*((1849/12500 : ℝ)+(1067/10000 : ℝ)))^(4173/1024 : ℝ) := by
    rw [show (1373541411280066103/1374000000000000000 : ℝ)+(12475381463/6870000000000 : ℝ)*((1849/12500 : ℝ)+(1067/10000 : ℝ))=(400051443262209/400000000000000 : ℝ) by norm_num, show 1+(10366628002118541/25000000000000000000 : ℝ)+(5477094092463933/50000000000000000000 : ℝ)=(10005242070019340203/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10366628002118541/25000000000000000000 : ℝ) ≤ ((1373541411280066103/1374000000000000000 : ℝ)+2*(12475381463/6870000000000 : ℝ)*(1849/12500 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (1373541411280066103/1374000000000000000 : ℝ)+2*(12475381463/6870000000000 : ℝ)*(1849/12500 : ℝ)=(2000406920888601/2000000000000000 : ℝ) by norm_num, show 1+2*(10366628002118541/25000000000000000000 : ℝ)=(12510366628002118541/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1373541411280066103/1374000000000000000 : ℝ)*(X 1 0+X 2 0)+(12475381463/6870000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (1067/10000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (1373541411280066103/1374000000000000000 : ℝ)) (alpha := (12475381463/6870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1373541411280066103/1374000000000000000 : ℝ)*(X 0 1+X 2 1)+(12475381463/6870000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (1067/10000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (1373541411280066103/1374000000000000000 : ℝ)) (alpha := (12475381463/6870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1373541411280066103/1374000000000000000 : ℝ)*(X 0 2+X 1 2)+(12475381463/6870000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (1067/10000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (1373541411280066103/1374000000000000000 : ℝ)) (alpha := (12475381463/6870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2160394077/10000000000 : ℝ)*X 0 0+(270066421/500000000 : ℝ)*X 0 1+(5257923137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346850323/10000000000 : ℝ)*X 1 0+(-558315589/2500000000 : ℝ)*X 1 1+(1051584719/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673425171/5000000000 : ℝ)*X 2 0+(657240419/1250000000 : ℝ)*X 2 1+(-2233262651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362539029/10000000000 : ℝ)*X 0 0+(2110938281/5000000000 : ℝ)*X 0 1+(4507849959/10000000000 : ℝ)*X 0 2+(4362539029/10000000000 : ℝ)*X 1 0+(2110938281/5000000000 : ℝ)*X 1 1+(4507849959/10000000000 : ℝ)*X 1 2+(4362539029/10000000000 : ℝ)*X 2 0+(2110938281/5000000000 : ℝ)*X 2 1+(4507849959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1080200561/5000000000 : ℝ)*X 0 0+(1051666079/2000000000 : ℝ)*X 0 1+(5400919471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310487851/10000000000 : ℝ)*X 1 0+(-2090266519/10000000000 : ℝ)*X 1 1+(5400919493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212419513/400000000 : ℝ)*X 2 0+(675114979/1250000000 : ℝ)*X 2 1+(-522566523/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362552931/10000000000 : ℝ)*X 0 0+(1126759539/2500000000 : ℝ)*X 0 1+(4222691749/10000000000 : ℝ)*X 0 2+(4362552931/10000000000 : ℝ)*X 1 0+(1126759539/2500000000 : ℝ)*X 1 1+(4222691749/10000000000 : ℝ)*X 1 2+(4362552931/10000000000 : ℝ)*X 2 0+(1126759539/2500000000 : ℝ)*X 2 1+(4222691749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44608770982807951820898351/5725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53218471/25000000000000 : ℝ)*(base19) + (423767651/100000000000000 : ℝ)*(base23) + (59737949/100000000000000 : ℝ)*(lower2) + (280108409/100000000000000 : ℝ)*(upper3) + (79625231/50000000000000 : ℝ)*(lower4) + (2617532966431783/50000000000000 : ℝ)*(major0) + (2617532966431783/50000000000000 : ℝ)*(major1) + (2617532966431783/50000000000000 : ℝ)*(major2) + (6973268235872033/100000000000000 : ℝ)*(sp0) + (6973277828434651/100000000000000 : ℝ)*(sp1) + (1743319404385221/25000000000000 : ℝ)*(sp2) + (699367799605921/20000000000000 : ℝ)*(sp3) + (9805436503/100000000000000 : ℝ)*(sp4) + (2913331629/20000000000000 : ℝ)*(sp7) + (13987414258751/400000000000 : ℝ)*(f.failure) + (1394655608261707/20000000000000 : ℝ)*(f.sum) + (1176998378449/137400000000000000000000000 : ℝ)*base65 + (59702363845516117/22900000000000000000000000000000 : ℝ)*base68 + (215567680203383883/22900000000000000000000000000000 : ℝ)*base69 + (13578010844283883/22900000000000000000000000000000 : ℝ)*base71 + (702917426839/343500000000000000000000000 : ℝ)*base73 + (283816254541483883/22900000000000000000000000000000 : ℝ)*base75 + (47226353584783883/22900000000000000000000000000000 : ℝ)*base77 + (547036877487783883/22900000000000000000000000000000 : ℝ)*base79 + (57724380689/42937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (343353/40000000000000000000 : ℝ)*base90 + (343353/40000000000000000000 : ℝ)*base92 + (343353/40000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131293964650375447151926911/11450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170874741/20000000000000 : ℝ)*(base19) + (1254561153/100000000000000 : ℝ)*(base23) + (5343441/10000000000000 : ℝ)*(lower2) + (20418113/5000000000000 : ℝ)*(upper3) + (141293057/100000000000000 : ℝ)*(lower4) + (4604173/20000000000000 : ℝ)*(upper5) + (5264993771146263/100000000000000 : ℝ)*(major0) + (5264993771146263/100000000000000 : ℝ)*(major1) + (5264993771146263/100000000000000 : ℝ)*(major2) + (19648609183/50000000000000 : ℝ)*(sp2) + (7013142773999591/100000000000000 : ℝ)*(sp4) + (3506570959812943/50000000000000 : ℝ)*(sp5) + (7013102222220073/100000000000000 : ℝ)*(sp6) + (879211096517217/25000000000000 : ℝ)*(sp7) + (879211096517217/25000000000000 : ℝ)*(f.failure) + (7013142773999591/100000000000000 : ℝ)*(f.sum) + (41040091829/7156250000000000000000000 : ℝ)*base66 + (135640061642325637/45800000000000000000000000000000 : ℝ)*base68 + (191018791045674363/45800000000000000000000000000000 : ℝ)*base69 + (173108398719874363/45800000000000000000000000000000 : ℝ)*base71 + (14785553/4472656250000000000000 : ℝ)*base74 + (493900628831074363/45800000000000000000000000000000 : ℝ)*base75 + (815921410096074363/45800000000000000000000000000000 : ℝ)*base77 + (162243041124274363/45800000000000000000000000000000 : ℝ)*base79 + (468040427/111816406250000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6362649/2500000000000000000000 : ℝ)*base89 + (6362649/2500000000000000000000 : ℝ)*base91 + (6362649/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1154_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1067/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1154_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1154_s5_0 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-43220099/200000000 : ℝ)*x 0 + (2697301381/5000000000 : ℝ)*x 1 + (26321239/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43220099/200000000 : ℝ)^8347 ≤ (6566013121961/50000000000000 : ℝ)^6299 := by
    have hnat : (43220099 : ℕ)^8347*50000000000000^6299 ≤ 6566013121961^6299*200000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43220099 200000000 6566013121961 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697301381/5000000000 : ℝ)^8347 ≤ (44137851804747/100000000000000 : ℝ)^6299 := by
    have hnat : (2697301381 : ℕ)^8347*100000000000000^6299 ≤ 44137851804747^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697301381 5000000000 44137851804747 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26321239/50000000 : ℝ)^8347 ≤ (10682530486603/25000000000000 : ℝ)^6299 := by
    have hnat : (26321239 : ℕ)^8347*25000000000000^6299 ≤ 10682530486603^6299*50000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26321239 50000000 10682530486603 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43220099/200000000 : ℝ), (2697301381/5000000000 : ℝ), (26321239/50000000 : ℝ)] ![(6566013121961/50000000000000 : ℝ), (44137851804747/100000000000000 : ℝ), (10682530486603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43220099/200000000 : ℝ)|^8347 ≤ (6566013121961/50000000000000 : ℝ)^6299
        have hw : |(-43220099/200000000 : ℝ)|=(43220099/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697301381/5000000000 : ℝ)|^8347 ≤ (44137851804747/100000000000000 : ℝ)^6299
        have hw : |(2697301381/5000000000 : ℝ)|=(2697301381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26321239/50000000 : ℝ)|^8347 ≤ (10682530486603/25000000000000 : ℝ)^6299
        have hw : |(26321239/50000000 : ℝ)|=(26321239/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s5_1 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672581021/5000000000 : ℝ)*x 0 + (-2227146179/10000000000 : ℝ)*x 1 + (2632123813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672581021/5000000000 : ℝ)^8347 ≤ (43602614420289/100000000000000 : ℝ)^6299 := by
    have hnat : (2672581021 : ℕ)^8347*100000000000000^6299 ≤ 43602614420289^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672581021 5000000000 43602614420289 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2227146179/10000000000 : ℝ)^8347 ≤ (3416816370121/25000000000000 : ℝ)^6299 := by
    have hnat : (2227146179 : ℕ)^8347*25000000000000^6299 ≤ 3416816370121^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227146179 10000000000 3416816370121 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632123813/5000000000 : ℝ)^8347 ≤ (42730120074843/100000000000000 : ℝ)^6299 := by
    have hnat : (2632123813 : ℕ)^8347*100000000000000^6299 ≤ 42730120074843^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632123813 5000000000 42730120074843 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672581021/5000000000 : ℝ), (-2227146179/10000000000 : ℝ), (2632123813/5000000000 : ℝ)] ![(43602614420289/100000000000000 : ℝ), (3416816370121/25000000000000 : ℝ), (42730120074843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672581021/5000000000 : ℝ)|^8347 ≤ (43602614420289/100000000000000 : ℝ)^6299
        have hw : |(2672581021/5000000000 : ℝ)|=(2672581021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2227146179/10000000000 : ℝ)|^8347 ≤ (3416816370121/25000000000000 : ℝ)^6299
        have hw : |(-2227146179/10000000000 : ℝ)|=(2227146179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632123813/5000000000 : ℝ)|^8347 ≤ (42730120074843/100000000000000 : ℝ)^6299
        have hw : |(2632123813/5000000000 : ℝ)|=(2632123813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s5_2 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345162099/10000000000 : ℝ)*x 0 + (2632123831/5000000000 : ℝ)*x 1 + (-278393257/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345162099/10000000000 : ℝ)^8347 ≤ (21801307518219/50000000000000 : ℝ)^6299 := by
    have hnat : (5345162099 : ℕ)^8347*50000000000000^6299 ≤ 21801307518219^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345162099 10000000000 21801307518219 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632123831/5000000000 : ℝ)^8347 ≤ (2670632528879/6250000000000 : ℝ)^6299 := by
    have hnat : (2632123831 : ℕ)^8347*6250000000000^6299 ≤ 2670632528879^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632123831 5000000000 2670632528879 6250000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278393257/1250000000 : ℝ)^8347 ≤ (13667264480261/100000000000000 : ℝ)^6299 := by
    have hnat : (278393257 : ℕ)^8347*100000000000000^6299 ≤ 13667264480261^6299*1250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278393257 1250000000 13667264480261 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345162099/10000000000 : ℝ), (2632123831/5000000000 : ℝ), (-278393257/1250000000 : ℝ)] ![(21801307518219/50000000000000 : ℝ), (2670632528879/6250000000000 : ℝ), (13667264480261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345162099/10000000000 : ℝ)|^8347 ≤ (21801307518219/50000000000000 : ℝ)^6299
        have hw : |(5345162099/10000000000 : ℝ)|=(5345162099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632123831/5000000000 : ℝ)|^8347 ≤ (2670632528879/6250000000000 : ℝ)^6299
        have hw : |(2632123831/5000000000 : ℝ)|=(2632123831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278393257/1250000000 : ℝ)|^8347 ≤ (13667264480261/100000000000000 : ℝ)^6299
        have hw : |(-278393257/1250000000 : ℝ)|=(278393257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s5_3 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872579153/2000000000 : ℝ)*x 0 + (2117421481/5000000000 : ℝ)*x 1 + (2247395747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872579153/2000000000 : ℝ)^8347 ≤ (33316124746681/100000000000000 : ℝ)^6299 := by
    have hnat : (872579153 : ℕ)^8347*100000000000000^6299 ≤ 33316124746681^6299*2000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872579153 2000000000 33316124746681 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117421481/5000000000 : ℝ)^8347 ≤ (32026579808683/100000000000000 : ℝ)^6299 := by
    have hnat : (2117421481 : ℕ)^8347*100000000000000^6299 ≤ 32026579808683^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117421481 5000000000 32026579808683 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247395747/5000000000 : ℝ)^8347 ≤ (17328647716021/50000000000000 : ℝ)^6299 := by
    have hnat : (2247395747 : ℕ)^8347*50000000000000^6299 ≤ 17328647716021^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247395747 5000000000 17328647716021 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872579153/2000000000 : ℝ), (2117421481/5000000000 : ℝ), (2247395747/5000000000 : ℝ)] ![(33316124746681/100000000000000 : ℝ), (32026579808683/100000000000000 : ℝ), (17328647716021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872579153/2000000000 : ℝ)|^8347 ≤ (33316124746681/100000000000000 : ℝ)^6299
        have hw : |(872579153/2000000000 : ℝ)|=(872579153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117421481/5000000000 : ℝ)|^8347 ≤ (32026579808683/100000000000000 : ℝ)^6299
        have hw : |(2117421481/5000000000 : ℝ)|=(2117421481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247395747/5000000000 : ℝ)|^8347 ≤ (17328647716021/50000000000000 : ℝ)^6299
        have hw : |(2247395747/5000000000 : ℝ)|=(2247395747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s5_4 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-432201941/2000000000 : ℝ)*x 0 + (658073109/1250000000 : ℝ)*x 1 + (5394264821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432201941/2000000000 : ℝ)^8347 ≤ (13132064533931/100000000000000 : ℝ)^6299 := by
    have hnat : (432201941 : ℕ)^8347*100000000000000^6299 ≤ 13132064533931^6299*2000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432201941 2000000000 13132064533931 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658073109/1250000000 : ℝ)^8347 ≤ (8546749515833/20000000000000 : ℝ)^6299 := by
    have hnat : (658073109 : ℕ)^8347*20000000000000^6299 ≤ 8546749515833^6299*1250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658073109 1250000000 8546749515833 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394264821/10000000000 : ℝ)^8347 ≤ (1379193371133/3125000000000 : ℝ)^6299 := by
    have hnat : (5394264821 : ℕ)^8347*3125000000000^6299 ≤ 1379193371133^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394264821 10000000000 1379193371133 3125000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432201941/2000000000 : ℝ), (658073109/1250000000 : ℝ), (5394264821/10000000000 : ℝ)] ![(13132064533931/100000000000000 : ℝ), (8546749515833/20000000000000 : ℝ), (1379193371133/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432201941/2000000000 : ℝ)|^8347 ≤ (13132064533931/100000000000000 : ℝ)^6299
        have hw : |(-432201941/2000000000 : ℝ)|=(432201941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658073109/1250000000 : ℝ)|^8347 ≤ (8546749515833/20000000000000 : ℝ)^6299
        have hw : |(658073109/1250000000 : ℝ)|=(658073109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394264821/10000000000 : ℝ)|^8347 ≤ (1379193371133/3125000000000 : ℝ)^6299
        have hw : |(5394264821/10000000000 : ℝ)|=(5394264821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s5_5 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062421569/2000000000 : ℝ)*x 0 + (-524281953/2500000000 : ℝ)*x 1 + (5394265023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062421569/2000000000 : ℝ)^8347 ≤ (43245670781011/100000000000000 : ℝ)^6299 := by
    have hnat : (1062421569 : ℕ)^8347*100000000000000^6299 ≤ 43245670781011^6299*2000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062421569 2000000000 43245670781011 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524281953/2500000000 : ℝ)^8347 ≤ (1262013914771/10000000000000 : ℝ)^6299 := by
    have hnat : (524281953 : ℕ)^8347*10000000000000^6299 ≤ 1262013914771^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524281953 2500000000 1262013914771 10000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394265023/10000000000 : ℝ)^8347 ≤ (44134190066301/100000000000000 : ℝ)^6299 := by
    have hnat : (5394265023 : ℕ)^8347*100000000000000^6299 ≤ 44134190066301^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394265023 10000000000 44134190066301 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062421569/2000000000 : ℝ), (-524281953/2500000000 : ℝ), (5394265023/10000000000 : ℝ)] ![(43245670781011/100000000000000 : ℝ), (1262013914771/10000000000000 : ℝ), (44134190066301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062421569/2000000000 : ℝ)|^8347 ≤ (43245670781011/100000000000000 : ℝ)^6299
        have hw : |(1062421569/2000000000 : ℝ)|=(1062421569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524281953/2500000000 : ℝ)|^8347 ≤ (1262013914771/10000000000000 : ℝ)^6299
        have hw : |(-524281953/2500000000 : ℝ)|=(524281953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394265023/10000000000 : ℝ)|^8347 ≤ (44134190066301/100000000000000 : ℝ)^6299
        have hw : |(5394265023/10000000000 : ℝ)|=(5394265023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s5_6 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531210721/1000000000 : ℝ)*x 0 + (5394265501/10000000000 : ℝ)*x 1 + (-104856401/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531210721/1000000000 : ℝ)^8347 ≤ (10811415982683/25000000000000 : ℝ)^6299 := by
    have hnat : (531210721 : ℕ)^8347*25000000000000^6299 ≤ 10811415982683^6299*1000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531210721 1000000000 10811415982683 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394265501/10000000000 : ℝ)^8347 ≤ (8826839049737/20000000000000 : ℝ)^6299 := by
    have hnat : (5394265501 : ℕ)^8347*20000000000000^6299 ≤ 8826839049737^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394265501 10000000000 8826839049737 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104856401/500000000 : ℝ)^8347 ≤ (6310070403193/50000000000000 : ℝ)^6299 := by
    have hnat : (104856401 : ℕ)^8347*50000000000000^6299 ≤ 6310070403193^6299*500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104856401 500000000 6310070403193 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531210721/1000000000 : ℝ), (5394265501/10000000000 : ℝ), (-104856401/500000000 : ℝ)] ![(10811415982683/25000000000000 : ℝ), (8826839049737/20000000000000 : ℝ), (6310070403193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531210721/1000000000 : ℝ)|^8347 ≤ (10811415982683/25000000000000 : ℝ)^6299
        have hw : |(531210721/1000000000 : ℝ)|=(531210721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394265501/10000000000 : ℝ)|^8347 ≤ (8826839049737/20000000000000 : ℝ)^6299
        have hw : |(5394265501/10000000000 : ℝ)|=(5394265501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104856401/500000000 : ℝ)|^8347 ≤ (6310070403193/50000000000000 : ℝ)^6299
        have hw : |(-104856401/500000000 : ℝ)|=(104856401/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s5_7 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272681679/625000000 : ℝ)*x 0 + (1123530011/2500000000 : ℝ)*x 1 + (2117758151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272681679/625000000 : ℝ)^8347 ≤ (520566204027/1562500000000 : ℝ)^6299 := by
    have hnat : (272681679 : ℕ)^8347*1562500000000^6299 ≤ 520566204027^6299*625000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272681679 625000000 520566204027 1562500000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123530011/2500000000 : ℝ)^8347 ≤ (34650435069701/100000000000000 : ℝ)^6299 := by
    have hnat : (1123530011 : ℕ)^8347*100000000000000^6299 ≤ 34650435069701^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123530011 2500000000 34650435069701 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117758151/5000000000 : ℝ)^8347 ≤ (32033327849431/100000000000000 : ℝ)^6299 := by
    have hnat : (2117758151 : ℕ)^8347*100000000000000^6299 ≤ 32033327849431^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117758151 5000000000 32033327849431 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272681679/625000000 : ℝ), (1123530011/2500000000 : ℝ), (2117758151/5000000000 : ℝ)] ![(520566204027/1562500000000 : ℝ), (34650435069701/100000000000000 : ℝ), (32033327849431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272681679/625000000 : ℝ)|^8347 ≤ (520566204027/1562500000000 : ℝ)^6299
        have hw : |(272681679/625000000 : ℝ)|=(272681679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123530011/2500000000 : ℝ)|^8347 ≤ (34650435069701/100000000000000 : ℝ)^6299
        have hw : |(1123530011/2500000000 : ℝ)|=(1123530011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117758151/5000000000 : ℝ)|^8347 ≤ (32033327849431/100000000000000 : ℝ)^6299
        have hw : |(2117758151/5000000000 : ℝ)|=(2117758151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1154_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11333/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7047/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5599/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5599/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5599/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5599/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5599/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5599/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5599/50000 : ℝ) ^ (4173/1024 : ℝ) ≤ (6668554071300239/50000000000000000000 : ℝ) := by
    have hpowers : (5599/50000 : ℝ)^4173 ≤ (6668554071300239/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5599 : ℕ)^4173*50000000000000000000^1024 ≤ 6668554071300239^1024*50000^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5599 50000 6668554071300239 50000000000000000000 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5599/50000 : ℝ)) (X := (6668554071300239/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (4173/1024 : ℝ) ≤ (17731127011858333/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^4173 ≤ (17731127011858333/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4173*50000000000000000000^1024 ≤ 17731127011858333^1024*20000^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 17731127011858333 50000000000000000000 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (17731127011858333/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006668554071300239/25000000000000000000 : ℝ) ≤ (1250081810594557/1250000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (25006668554071300239/25000000000000000000 : ℝ)^1024 ≤ (1250081810594557/1250000000000000 : ℝ)^4173 := by
      have hnat : (25006668554071300239 : ℕ)^1024*1250000000000000^4173 ≤ 1250081810594557^4173*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006668554071300239 25000000000000000000 1250081810594557 1250000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250081810594557/1250000000000000 : ℝ)) (X := (25006668554071300239/25000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506099920270789643/12500000000000000000 : ℝ) ≤ (1000119725254609/1000000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (12506099920270789643/12500000000000000000 : ℝ)^1024 ≤ (1000119725254609/1000000000000000 : ℝ)^4173 := by
      have hnat : (12506099920270789643 : ℕ)^1024*1000000000000000^4173 ≤ 1000119725254609^4173*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506099920270789643 12500000000000000000 1000119725254609 1000000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000119725254609/1000000000000000 : ℝ)) (X := (12506099920270789643/12500000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017731127011858333/25000000000000000000 : ℝ) ≤ (2500435005083931/2500000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (25017731127011858333/25000000000000000000 : ℝ)^1024 ≤ (2500435005083931/2500000000000000 : ℝ)^4173 := by
      have hnat : (25017731127011858333 : ℕ)^1024*2500000000000000^4173 ≤ 2500435005083931^4173*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017731127011858333 25000000000000000000 2500435005083931 2500000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500435005083931/2500000000000000 : ℝ)) (X := (25017731127011858333/25000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6668554071300239/50000000000000000000 : ℝ) ≤ ((1897489490174294613/1898125000000000000 : ℝ)+2*(271383894817/151850000000000 : ℝ)*(5599/50000 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (1897489490174294613/1898125000000000000 : ℝ)+2*(271383894817/151850000000000 : ℝ)*(5599/50000 : ℝ)=(1250081810594557/1250000000000000 : ℝ) by norm_num, show 1+2*(6668554071300239/50000000000000000000 : ℝ)=(25006668554071300239/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17731127011858333/50000000000000000000 : ℝ)+(6668554071300239/50000000000000000000 : ℝ) ≤ ((1897489490174294613/1898125000000000000 : ℝ)+(271383894817/151850000000000 : ℝ)*((2847/20000 : ℝ)+(5599/50000 : ℝ)))^(4173/1024 : ℝ) := by
    rw [show (1897489490174294613/1898125000000000000 : ℝ)+(271383894817/151850000000000 : ℝ)*((2847/20000 : ℝ)+(5599/50000 : ℝ))=(1000119725254609/1000000000000000 : ℝ) by norm_num, show 1+(17731127011858333/50000000000000000000 : ℝ)+(6668554071300239/50000000000000000000 : ℝ)=(12506099920270789643/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17731127011858333/50000000000000000000 : ℝ) ≤ ((1897489490174294613/1898125000000000000 : ℝ)+2*(271383894817/151850000000000 : ℝ)*(2847/20000 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (1897489490174294613/1898125000000000000 : ℝ)+2*(271383894817/151850000000000 : ℝ)*(2847/20000 : ℝ)=(2500435005083931/2500000000000000 : ℝ) by norm_num, show 1+2*(17731127011858333/50000000000000000000 : ℝ)=(25017731127011858333/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1897489490174294613/1898125000000000000 : ℝ)*(X 1 0+X 2 0)+(271383894817/151850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1897489490174294613/1898125000000000000 : ℝ)) (alpha := (271383894817/151850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1897489490174294613/1898125000000000000 : ℝ)*(X 0 1+X 2 1)+(271383894817/151850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1897489490174294613/1898125000000000000 : ℝ)) (alpha := (271383894817/151850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1897489490174294613/1898125000000000000 : ℝ)*(X 0 2+X 1 2)+(271383894817/151850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1897489490174294613/1898125000000000000 : ℝ)) (alpha := (271383894817/151850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-43220099/200000000 : ℝ)*X 0 0+(2697301381/5000000000 : ℝ)*X 0 1+(26321239/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672581021/5000000000 : ℝ)*X 1 0+(-2227146179/10000000000 : ℝ)*X 1 1+(2632123813/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345162099/10000000000 : ℝ)*X 2 0+(2632123831/5000000000 : ℝ)*X 2 1+(-278393257/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872579153/2000000000 : ℝ)*X 0 0+(2117421481/5000000000 : ℝ)*X 0 1+(2247395747/5000000000 : ℝ)*X 0 2+(872579153/2000000000 : ℝ)*X 1 0+(2117421481/5000000000 : ℝ)*X 1 1+(2247395747/5000000000 : ℝ)*X 1 2+(872579153/2000000000 : ℝ)*X 2 0+(2117421481/5000000000 : ℝ)*X 2 1+(2247395747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-432201941/2000000000 : ℝ)*X 0 0+(658073109/1250000000 : ℝ)*X 0 1+(5394264821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062421569/2000000000 : ℝ)*X 1 0+(-524281953/2500000000 : ℝ)*X 1 1+(5394265023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531210721/1000000000 : ℝ)*X 2 0+(5394265501/10000000000 : ℝ)*X 2 1+(-104856401/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272681679/625000000 : ℝ)*X 0 0+(1123530011/2500000000 : ℝ)*X 0 1+(2117758151/5000000000 : ℝ)*X 0 2+(272681679/625000000 : ℝ)*X 1 0+(1123530011/2500000000 : ℝ)*X 1 1+(2117758151/5000000000 : ℝ)*X 1 2+(272681679/625000000 : ℝ)*X 2 0+(1123530011/2500000000 : ℝ)*X 2 1+(2117758151/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80506849295638550323929/15185000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9705753/4000000000000 : ℝ)*(base19) + (2734589/50000000000000 : ℝ)*(base23) + (18978559/25000000000000 : ℝ)*(upper3) + (10282227/6250000000000 : ℝ)*(upper4) + (13472279/12500000000000 : ℝ)*(upper5) + (2879567084503829/50000000000000 : ℝ)*(major0) + (2879567084503829/50000000000000 : ℝ)*(major1) + (2879567084503829/50000000000000 : ℝ)*(major2) + (3835677040497527/50000000000000 : ℝ)*(sp0) + (7671346571193783/100000000000000 : ℝ)*(sp1) + (7671344997962603/100000000000000 : ℝ)*(sp2) + (15387656321183/400000000000 : ℝ)*(sp3) + (7267157447/100000000000000 : ℝ)*(sp5) + (9077563273/100000000000000 : ℝ)*(sp6) + (15387656321183/400000000000 : ℝ)*(f.failure) + (3835677040497527/50000000000000 : ℝ)*(f.sum) + (39275197150539/7592500000000000000000000000 : ℝ)*base66 + (494242401085514323/94906250000000000000000000000000 : ℝ)*base68 + (9331959698110677/94906250000000000000000000000000 : ℝ)*base69 + (1192999603679608073/94906250000000000000000000000000 : ℝ)*base72 + (24716581112057/15185000000000000000000000000 : ℝ)*base73 + (19083373859483073/94906250000000000000000000000000 : ℝ)*base76 + (236988414484079427/94906250000000000000000000000000 : ℝ)*base77 + (48812128414266927/94906250000000000000000000000000 : ℝ)*base79 + (8214668360463/3796250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (282151/40000000000000000000 : ℝ)*base89 + (282151/40000000000000000000 : ℝ)*base91 + (282151/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (367864435112834511352917837/47453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (461395647/25000000000000 : ℝ)*(base19) + (1892326669/100000000000000 : ℝ)*(base23) + (2488697/2000000000000 : ℝ)*(upper3) + (477270121/100000000000000 : ℝ)*(lower4) + (1447273969401129/25000000000000 : ℝ)*(major0) + (1447273969401129/25000000000000 : ℝ)*(major1) + (1447273969401129/25000000000000 : ℝ)*(major2) + (16946945749/25000000000000 : ℝ)*(sp1) + (39524116179/50000000000000 : ℝ)*(sp2) + (3523132393/50000000000000 : ℝ)*(sp3) + (7711263970859787/100000000000000 : ℝ)*(sp4) + (7711194337494203/100000000000000 : ℝ)*(sp5) + (7711183030300759/100000000000000 : ℝ)*(sp6) + (966730119919741/25000000000000 : ℝ)*(sp7) + (3866927525943749/100000000000000 : ℝ)*(f.failure) + (7711263970859787/100000000000000 : ℝ)*(f.sum) + (29068353237791/15185000000000000000000000000 : ℝ)*base66 + (640793934056206923/47453125000000000000000000000000 : ℝ)*base68 + (256098498160126899/23726562500000000000000000000000 : ℝ)*base70 + (20904378089788113/11863281250000000000000000000000 : ℝ)*base71 + (17504196813009/3796250000000000000000000000 : ℝ)*base74 + (211883214421493137/11863281250000000000000000000000 : ℝ)*base76 + (162920630809074327/47453125000000000000000000000000 : ℝ)*base77 + (422153549939564399/23726562500000000000000000000000 : ℝ)*base80 + (1440446154639/237265625000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3085853/10000000000000000000000 : ℝ)*base89 + (3085853/10000000000000000000000 : ℝ)*base91 + (3085853/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1154_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1154_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1154_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16467/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1154_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1154_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1154_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16467/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1154_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
