-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1643_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:20.673746+00:00
-- url     : https://prove2.me/submissions/493c3e11-80a9-4b94-94ff-d8ea3a0ce6ac

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
theorem support_rectangle_w1643_s3_0 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1624572369/10000000000 : ℝ)*x 0 + (5449708241/10000000000 : ℝ)*x 1 + (1295837421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1624572369/10000000000 : ℝ)^4891 ≤ (627507654769/6250000000000 : ℝ)^3867 := by
    have hnat : (1624572369 : ℕ)^4891*6250000000000^3867 ≤ 627507654769^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624572369 10000000000 627507654769 6250000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5449708241/10000000000 : ℝ)^4891 ≤ (46404877979/100000000000 : ℝ)^3867 := by
    have hnat : (5449708241 : ℕ)^4891*100000000000^3867 ≤ 46404877979^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449708241 10000000000 46404877979 100000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295837421/2500000000 : ℝ)^4891 ≤ (1742199981029/4000000000000 : ℝ)^3867 := by
    have hnat : (1295837421 : ℕ)^4891*4000000000000^3867 ≤ 1742199981029^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295837421 2500000000 1742199981029 4000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1624572369/10000000000 : ℝ), (5449708241/10000000000 : ℝ), (1295837421/2500000000 : ℝ)] ![(627507654769/6250000000000 : ℝ), (46404877979/100000000000 : ℝ), (1742199981029/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1624572369/10000000000 : ℝ)|^4891 ≤ (627507654769/6250000000000 : ℝ)^3867
        have hw : |(-1624572369/10000000000 : ℝ)|=(1624572369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5449708241/10000000000 : ℝ)|^4891 ≤ (46404877979/100000000000 : ℝ)^3867
        have hw : |(5449708241/10000000000 : ℝ)|=(5449708241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295837421/2500000000 : ℝ)|^4891 ≤ (1742199981029/4000000000000 : ℝ)^3867
        have hw : |(1295837421/2500000000 : ℝ)|=(1295837421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s3_1 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674410047/5000000000 : ℝ)*x 0 + (-1761732527/10000000000 : ℝ)*x 1 + (5183349671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674410047/5000000000 : ℝ)^4891 ≤ (22660496336823/50000000000000 : ℝ)^3867 := by
    have hnat : (2674410047 : ℕ)^4891*50000000000000^3867 ≤ 22660496336823^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674410047 5000000000 22660496336823 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1761732527/10000000000 : ℝ)^4891 ≤ (1112400792649/10000000000000 : ℝ)^3867 := by
    have hnat : (1761732527 : ℕ)^4891*10000000000000^3867 ≤ 1112400792649^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761732527 10000000000 1112400792649 10000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183349671/10000000000 : ℝ)^4891 ≤ (43554999387561/100000000000000 : ℝ)^3867 := by
    have hnat : (5183349671 : ℕ)^4891*100000000000000^3867 ≤ 43554999387561^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183349671 10000000000 43554999387561 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674410047/5000000000 : ℝ), (-1761732527/10000000000 : ℝ), (5183349671/10000000000 : ℝ)] ![(22660496336823/50000000000000 : ℝ), (1112400792649/10000000000000 : ℝ), (43554999387561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674410047/5000000000 : ℝ)|^4891 ≤ (22660496336823/50000000000000 : ℝ)^3867
        have hw : |(2674410047/5000000000 : ℝ)|=(2674410047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1761732527/10000000000 : ℝ)|^4891 ≤ (1112400792649/10000000000000 : ℝ)^3867
        have hw : |(-1761732527/10000000000 : ℝ)|=(1761732527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183349671/10000000000 : ℝ)|^4891 ≤ (43554999387561/100000000000000 : ℝ)^3867
        have hw : |(5183349671/10000000000 : ℝ)|=(5183349671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s3_2 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674410043/5000000000 : ℝ)*x 0 + (5183349661/10000000000 : ℝ)*x 1 + (-1761732551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674410043/5000000000 : ℝ)^4891 ≤ (5665124073489/12500000000000 : ℝ)^3867 := by
    have hnat : (2674410043 : ℕ)^4891*12500000000000^3867 ≤ 5665124073489^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674410043 5000000000 5665124073489 12500000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183349661/10000000000 : ℝ)^4891 ≤ (43554999281281/100000000000000 : ℝ)^3867 := by
    have hnat : (5183349661 : ℕ)^4891*100000000000000^3867 ≤ 43554999281281^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183349661 10000000000 43554999281281 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1761732551/10000000000 : ℝ)^4891 ≤ (11124008118161/100000000000000 : ℝ)^3867 := by
    have hnat : (1761732551 : ℕ)^4891*100000000000000^3867 ≤ 11124008118161^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761732551 10000000000 11124008118161 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674410043/5000000000 : ℝ), (5183349661/10000000000 : ℝ), (-1761732551/10000000000 : ℝ)] ![(5665124073489/12500000000000 : ℝ), (43554999281281/100000000000000 : ℝ), (11124008118161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674410043/5000000000 : ℝ)|^4891 ≤ (5665124073489/12500000000000 : ℝ)^3867
        have hw : |(2674410043/5000000000 : ℝ)|=(2674410043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183349661/10000000000 : ℝ)|^4891 ≤ (43554999281281/100000000000000 : ℝ)^3867
        have hw : |(5183349661/10000000000 : ℝ)|=(5183349661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1761732551/10000000000 : ℝ)|^4891 ≤ (11124008118161/100000000000000 : ℝ)^3867
        have hw : |(-1761732551/10000000000 : ℝ)|=(1761732551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s3_3 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093056619/5000000000 : ℝ)*x 0 + (1927395173/5000000000 : ℝ)*x 1 + (4537853471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093056619/5000000000 : ℝ)^4891 ≤ (33240283423403/100000000000000 : ℝ)^3867 := by
    have hnat : (2093056619 : ℕ)^4891*100000000000000^3867 ≤ 33240283423403^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093056619 5000000000 33240283423403 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927395173/5000000000 : ℝ)^4891 ≤ (7487068445423/25000000000000 : ℝ)^3867 := by
    have hnat : (1927395173 : ℕ)^4891*25000000000000^3867 ≤ 7487068445423^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927395173 5000000000 7487068445423 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4537853471/10000000000 : ℝ)^4891 ≤ (4601430347799/12500000000000 : ℝ)^3867 := by
    have hnat : (4537853471 : ℕ)^4891*12500000000000^3867 ≤ 4601430347799^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537853471 10000000000 4601430347799 12500000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093056619/5000000000 : ℝ), (1927395173/5000000000 : ℝ), (4537853471/10000000000 : ℝ)] ![(33240283423403/100000000000000 : ℝ), (7487068445423/25000000000000 : ℝ), (4601430347799/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093056619/5000000000 : ℝ)|^4891 ≤ (33240283423403/100000000000000 : ℝ)^3867
        have hw : |(2093056619/5000000000 : ℝ)|=(2093056619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1927395173/5000000000 : ℝ)|^4891 ≤ (7487068445423/25000000000000 : ℝ)^3867
        have hw : |(1927395173/5000000000 : ℝ)|=(1927395173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4537853471/10000000000 : ℝ)|^4891 ≤ (4601430347799/12500000000000 : ℝ)^3867
        have hw : |(4537853471/10000000000 : ℝ)|=(4537853471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s3_4 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1624638029/10000000000 : ℝ)*x 0 + (1296340181/2500000000 : ℝ)*x 1 + (5447675853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1624638029/10000000000 : ℝ)^4891 ≤ (5020317861783/50000000000000 : ℝ)^3867 := by
    have hnat : (1624638029 : ℕ)^4891*50000000000000^3867 ≤ 5020317861783^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624638029 10000000000 5020317861783 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296340181/2500000000 : ℝ)^4891 ≤ (21788186964799/50000000000000 : ℝ)^3867 := by
    have hnat : (1296340181 : ℕ)^4891*50000000000000^3867 ≤ 21788186964799^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296340181 2500000000 21788186964799 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447675853/10000000000 : ℝ)^4891 ≤ (4638299033337/10000000000000 : ℝ)^3867 := by
    have hnat : (5447675853 : ℕ)^4891*10000000000000^3867 ≤ 4638299033337^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447675853 10000000000 4638299033337 10000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1624638029/10000000000 : ℝ), (1296340181/2500000000 : ℝ), (5447675853/10000000000 : ℝ)] ![(5020317861783/50000000000000 : ℝ), (21788186964799/50000000000000 : ℝ), (4638299033337/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1624638029/10000000000 : ℝ)|^4891 ≤ (5020317861783/50000000000000 : ℝ)^3867
        have hw : |(-1624638029/10000000000 : ℝ)|=(1624638029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296340181/2500000000 : ℝ)|^4891 ≤ (21788186964799/50000000000000 : ℝ)^3867
        have hw : |(1296340181/2500000000 : ℝ)|=(1296340181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447675853/10000000000 : ℝ)|^4891 ≤ (4638299033337/10000000000000 : ℝ)^3867
        have hw : |(5447675853/10000000000 : ℝ)|=(5447675853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s3_5 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277722447/10000000000 : ℝ)*x 0 + (-1497406387/10000000000 : ℝ)*x 1 + (5447675827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277722447/10000000000 : ℝ)^4891 ≤ (44560399127761/100000000000000 : ℝ)^3867 := by
    have hnat : (5277722447 : ℕ)^4891*100000000000000^3867 ≤ 44560399127761^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277722447 10000000000 44560399127761 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1497406387/10000000000 : ℝ)^4891 ≤ (566038175249/6250000000000 : ℝ)^3867 := by
    have hnat : (1497406387 : ℕ)^4891*6250000000000^3867 ≤ 566038175249^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1497406387 10000000000 566038175249 6250000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447675827/10000000000 : ℝ)^4891 ≤ (46382990053379/100000000000000 : ℝ)^3867 := by
    have hnat : (5447675827 : ℕ)^4891*100000000000000^3867 ≤ 46382990053379^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447675827 10000000000 46382990053379 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277722447/10000000000 : ℝ), (-1497406387/10000000000 : ℝ), (5447675827/10000000000 : ℝ)] ![(44560399127761/100000000000000 : ℝ), (566038175249/6250000000000 : ℝ), (46382990053379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277722447/10000000000 : ℝ)|^4891 ≤ (44560399127761/100000000000000 : ℝ)^3867
        have hw : |(5277722447/10000000000 : ℝ)|=(5277722447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1497406387/10000000000 : ℝ)|^4891 ≤ (566038175249/6250000000000 : ℝ)^3867
        have hw : |(-1497406387/10000000000 : ℝ)|=(1497406387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447675827/10000000000 : ℝ)|^4891 ≤ (46382990053379/100000000000000 : ℝ)^3867
        have hw : |(5447675827/10000000000 : ℝ)|=(5447675827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s3_6 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277722467/10000000000 : ℝ)*x 0 + (1361918979/2500000000 : ℝ)*x 1 + (-748703117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277722467/10000000000 : ℝ)^4891 ≤ (44560399341339/100000000000000 : ℝ)^3867 := by
    have hnat : (5277722467 : ℕ)^4891*100000000000000^3867 ≤ 44560399341339^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277722467 10000000000 44560399341339 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361918979/2500000000 : ℝ)^4891 ≤ (46382991011811/100000000000000 : ℝ)^3867 := by
    have hnat : (1361918979 : ℕ)^4891*100000000000000^3867 ≤ 46382991011811^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361918979 2500000000 46382991011811 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748703117/5000000000 : ℝ)^4891 ≤ (4528304816783/50000000000000 : ℝ)^3867 := by
    have hnat : (748703117 : ℕ)^4891*50000000000000^3867 ≤ 4528304816783^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748703117 5000000000 4528304816783 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277722467/10000000000 : ℝ), (1361918979/2500000000 : ℝ), (-748703117/5000000000 : ℝ)] ![(44560399341339/100000000000000 : ℝ), (46382991011811/100000000000000 : ℝ), (4528304816783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277722467/10000000000 : ℝ)|^4891 ≤ (44560399341339/100000000000000 : ℝ)^3867
        have hw : |(5277722467/10000000000 : ℝ)|=(5277722467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361918979/2500000000 : ℝ)|^4891 ≤ (46382991011811/100000000000000 : ℝ)^3867
        have hw : |(1361918979/2500000000 : ℝ)|=(1361918979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-748703117/5000000000 : ℝ)|^4891 ≤ (4528304816783/50000000000000 : ℝ)^3867
        have hw : |(-748703117/5000000000 : ℝ)|=(748703117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s3_7 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093140437/5000000000 : ℝ)*x 0 + (226634799/500000000 : ℝ)*x 1 + (96500061/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093140437/5000000000 : ℝ)^4891 ≤ (16620983527037/50000000000000 : ℝ)^3867 := by
    have hnat : (2093140437 : ℕ)^4891*50000000000000^3867 ≤ 16620983527037^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093140437 5000000000 16620983527037 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226634799/500000000 : ℝ)^4891 ≤ (7351706770831/20000000000000 : ℝ)^3867 := by
    have hnat : (226634799 : ℕ)^4891*20000000000000^3867 ≤ 7351706770831^3867*500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226634799 500000000 7351706770831 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96500061/250000000 : ℝ)^4891 ≤ (29999499077871/100000000000000 : ℝ)^3867 := by
    have hnat : (96500061 : ℕ)^4891*100000000000000^3867 ≤ 29999499077871^3867*250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96500061 250000000 29999499077871 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093140437/5000000000 : ℝ), (226634799/500000000 : ℝ), (96500061/250000000 : ℝ)] ![(16620983527037/50000000000000 : ℝ), (7351706770831/20000000000000 : ℝ), (29999499077871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093140437/5000000000 : ℝ)|^4891 ≤ (16620983527037/50000000000000 : ℝ)^3867
        have hw : |(2093140437/5000000000 : ℝ)|=(2093140437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226634799/500000000 : ℝ)|^4891 ≤ (7351706770831/20000000000000 : ℝ)^3867
        have hw : |(226634799/500000000 : ℝ)|=(226634799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(96500061/250000000 : ℝ)|^4891 ≤ (29999499077871/100000000000000 : ℝ)^3867
        have hw : |(96500061/250000000 : ℝ)|=(96500061/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1643_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2111/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2657/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16287/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2111/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2111/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2111/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2111/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2111/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2111/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2111/20000 : ℝ) ^ (4887/1024 : ℝ) ≤ (2185207011429943/100000000000000000000 : ℝ) := by
    have hpowers : (2111/20000 : ℝ)^4887 ≤ (2185207011429943/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2111 : ℕ)^4887*100000000000000000000^1024 ≤ 2185207011429943^1024*20000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2111 20000 2185207011429943 100000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2111/20000 : ℝ)) (X := (2185207011429943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16369/100000 : ℝ) ^ (4887/1024 : ℝ) ≤ (17739909785155097/100000000000000000000 : ℝ) := by
    have hpowers : (16369/100000 : ℝ)^4887 ≤ (17739909785155097/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16369 : ℕ)^4887*100000000000000000000^1024 ≤ 17739909785155097^1024*100000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16369 100000 17739909785155097 100000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16369/100000 : ℝ)) (X := (17739909785155097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002185207011429943/50000000000000000000 : ℝ) ≤ (5000045787054003/5000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (50002185207011429943/50000000000000000000 : ℝ)^1024 ≤ (5000045787054003/5000000000000000 : ℝ)^4887 := by
      have hnat : (50002185207011429943 : ℕ)^1024*5000000000000000^4887 ≤ 5000045787054003^4887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002185207011429943 50000000000000000000 5000045787054003 5000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000045787054003/5000000000000000 : ℝ)) (X := (50002185207011429943/50000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250249063959957313/1250000000000000000 : ℝ) ≤ (10000417469061171/10000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (1250249063959957313/1250000000000000000 : ℝ)^1024 ≤ (10000417469061171/10000000000000000 : ℝ)^4887 := by
      have hnat : (1250249063959957313 : ℕ)^1024*10000000000000000^4887 ≤ 10000417469061171^4887*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250249063959957313 1250000000000000000 10000417469061171 10000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000417469061171/10000000000000000 : ℝ)) (X := (1250249063959957313/1250000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017739909785155097/50000000000000000000 : ℝ) ≤ (39065403765681/39062500000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (50017739909785155097/50000000000000000000 : ℝ)^1024 ≤ (39065403765681/39062500000000 : ℝ)^4887 := by
      have hnat : (50017739909785155097 : ℕ)^1024*39062500000000^4887 ≤ 39065403765681^4887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017739909785155097 50000000000000000000 39065403765681 39062500000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39065403765681/39062500000000 : ℝ)) (X := (50017739909785155097/50000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2185207011429943/100000000000000000000 : ℝ) ≤ ((9688942128233772289/9690000000000000000 : ℝ)+2*(21726330211/38760000000000 : ℝ)*(2111/20000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (9688942128233772289/9690000000000000000 : ℝ)+2*(21726330211/38760000000000 : ℝ)*(2111/20000 : ℝ)=(5000045787054003/5000000000000000 : ℝ) by norm_num, show 1+2*(2185207011429943/100000000000000000000 : ℝ)=(50002185207011429943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17739909785155097/100000000000000000000 : ℝ)+(2185207011429943/100000000000000000000 : ℝ) ≤ ((9688942128233772289/9690000000000000000 : ℝ)+(21726330211/38760000000000 : ℝ)*((16369/100000 : ℝ)+(2111/20000 : ℝ)))^(4887/1024 : ℝ) := by
    rw [show (9688942128233772289/9690000000000000000 : ℝ)+(21726330211/38760000000000 : ℝ)*((16369/100000 : ℝ)+(2111/20000 : ℝ))=(10000417469061171/10000000000000000 : ℝ) by norm_num, show 1+(17739909785155097/100000000000000000000 : ℝ)+(2185207011429943/100000000000000000000 : ℝ)=(1250249063959957313/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17739909785155097/100000000000000000000 : ℝ) ≤ ((9688942128233772289/9690000000000000000 : ℝ)+2*(21726330211/38760000000000 : ℝ)*(16369/100000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (9688942128233772289/9690000000000000000 : ℝ)+2*(21726330211/38760000000000 : ℝ)*(16369/100000 : ℝ)=(39065403765681/39062500000000 : ℝ) by norm_num, show 1+2*(17739909785155097/100000000000000000000 : ℝ)=(50017739909785155097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9688942128233772289/9690000000000000000 : ℝ)*(X 1 0+X 2 0)+(21726330211/38760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (2111/20000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (9688942128233772289/9690000000000000000 : ℝ)) (alpha := (21726330211/38760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9688942128233772289/9690000000000000000 : ℝ)*(X 0 1+X 2 1)+(21726330211/38760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (2111/20000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (9688942128233772289/9690000000000000000 : ℝ)) (alpha := (21726330211/38760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9688942128233772289/9690000000000000000 : ℝ)*(X 0 2+X 1 2)+(21726330211/38760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (2111/20000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (9688942128233772289/9690000000000000000 : ℝ)) (alpha := (21726330211/38760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1624572369/10000000000 : ℝ)*X 0 0+(5449708241/10000000000 : ℝ)*X 0 1+(1295837421/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674410047/5000000000 : ℝ)*X 1 0+(-1761732527/10000000000 : ℝ)*X 1 1+(5183349671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674410043/5000000000 : ℝ)*X 2 0+(5183349661/10000000000 : ℝ)*X 2 1+(-1761732551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2093056619/5000000000 : ℝ)*X 0 0+(1927395173/5000000000 : ℝ)*X 0 1+(4537853471/10000000000 : ℝ)*X 0 2+(2093056619/5000000000 : ℝ)*X 1 0+(1927395173/5000000000 : ℝ)*X 1 1+(4537853471/10000000000 : ℝ)*X 1 2+(2093056619/5000000000 : ℝ)*X 2 0+(1927395173/5000000000 : ℝ)*X 2 1+(4537853471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1624638029/10000000000 : ℝ)*X 0 0+(1296340181/2500000000 : ℝ)*X 0 1+(5447675853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277722447/10000000000 : ℝ)*X 1 0+(-1497406387/10000000000 : ℝ)*X 1 1+(5447675827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277722467/10000000000 : ℝ)*X 2 0+(1361918979/2500000000 : ℝ)*X 2 1+(-748703117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2093140437/5000000000 : ℝ)*X 0 0+(226634799/500000000 : ℝ)*X 0 1+(96500061/250000000 : ℝ)*X 0 2+(2093140437/5000000000 : ℝ)*X 1 0+(226634799/500000000 : ℝ)*X 1 1+(96500061/250000000 : ℝ)*X 1 2+(2093140437/5000000000 : ℝ)*X 2 0+(226634799/500000000 : ℝ)*X 2 1+(96500061/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4640539794971588483637/646000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1105438431/100000000000000 : ℝ)*(base19) + (202986769/20000000000000 : ℝ)*(base23) + (5675723/12500000000000 : ℝ)*(lower2) + (185201521/100000000000000 : ℝ)*(upper3) + (1044783/1000000000000 : ℝ)*(upper5) + (521836947542061/20000000000000 : ℝ)*(major0) + (521836947542061/20000000000000 : ℝ)*(major1) + (521836947542061/20000000000000 : ℝ)*(major2) + (375435181307143/10000000000000 : ℝ)*(sp0) + (1877181830073529/50000000000000 : ℝ)*(sp1) + (938590937662911/25000000000000 : ℝ)*(sp2) + (1463998550268323/100000000000000 : ℝ)*(sp3) + (12952514059/100000000000000 : ℝ)*(sp4) + (5920116857/100000000000000 : ℝ)*(sp7) + (73200223519259/5000000000000 : ℝ)*(f.failure) + (3754364765585489/100000000000000 : ℝ)*(f.sum) + (175725065321/646000000000000000000000000 : ℝ)*base66 + (314010585560567457/64600000000000000000000000000000 : ℝ)*base68 + (563324747277832543/64600000000000000000000000000000 : ℝ)*base69 + (141321327091432543/64600000000000000000000000000000 : ℝ)*base71 + (2970064952807/646000000000000000000000000 : ℝ)*base74 + (100677494348767457/64600000000000000000000000000000 : ℝ)*base76 + (258199656684232543/64600000000000000000000000000000 : ℝ)*base77 + (8285874795367457/64600000000000000000000000000000 : ℝ)*base80 + (2499373300411/646000000000000000000000000 : ℝ)*base81 + (799363/500000000000000000000 : ℝ)*base89 + (799363/500000000000000000000 : ℝ)*base91 + (799363/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (115413643770075613495392953/20187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (218779389/25000000000000 : ℝ)*(base19) + (1070477811/100000000000000 : ℝ)*(base23) + (73305489/100000000000000 : ℝ)*(upper2) + (116375027/100000000000000 : ℝ)*(upper3) + (7824767/5000000000000 : ℝ)*(upper5) + (331173082634041/12500000000000 : ℝ)*(major0) + (331173082634041/12500000000000 : ℝ)*(major1) + (331173082634041/12500000000000 : ℝ)*(major2) + (257347887/2500000000000 : ℝ)*(sp1) + (1341298541/10000000000000 : ℝ)*(sp2) + (47652607802243/1250000000000 : ℝ)*(sp4) + (953049363786601/25000000000000 : ℝ)*(sp5) + (3812194140716219/100000000000000 : ℝ)*(sp6) + (59462420295829/4000000000000 : ℝ)*(sp7) + (59462420295829/4000000000000 : ℝ)*(f.failure) + (47652607802243/1250000000000 : ℝ)*(f.sum) + (702981248597/484500000000000000000000000 : ℝ)*base65 + (1353452939809139849/121125000000000000000000000000000 : ℝ)*base67 + (1294582403441639849/121125000000000000000000000000000 : ℝ)*base69 + (711484468588889849/121125000000000000000000000000000 : ℝ)*base71 + (756230949889/242250000000000000000000000 : ℝ)*base73 + (1155346688305139849/121125000000000000000000000000000 : ℝ)*base75 + (1281165403785764849/121125000000000000000000000000000 : ℝ)*base77 + (838185608643389849/121125000000000000000000000000000 : ℝ)*base79 + (41248953077/60562500000000000000000000 : ℝ)*base82 + (768147/400000000000000000000 : ℝ)*base90 + (768147/400000000000000000000 : ℝ)*base92 + (768147/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1643_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2111/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2657/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1643_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1643_s4_0 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1624626577/10000000000 : ℝ)*x 0 + (2724718941/5000000000 : ℝ)*x 1 + (5183583783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1624626577/10000000000 : ℝ)^4891 ≤ (2510136551461/25000000000000 : ℝ)^3867 := by
    have hnat : (1624626577 : ℕ)^4891*25000000000000^3867 ≤ 2510136551461^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624626577 10000000000 2510136551461 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724718941/5000000000 : ℝ)^4891 ≤ (11600491560991/25000000000000 : ℝ)^3867 := by
    have hnat : (2724718941 : ℕ)^4891*25000000000000^3867 ≤ 11600491560991^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724718941 5000000000 11600491560991 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183583783/10000000000 : ℝ)^4891 ≤ (21778743770811/50000000000000 : ℝ)^3867 := by
    have hnat : (5183583783 : ℕ)^4891*50000000000000^3867 ≤ 21778743770811^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183583783 10000000000 21778743770811 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1624626577/10000000000 : ℝ), (2724718941/5000000000 : ℝ), (5183583783/10000000000 : ℝ)] ![(2510136551461/25000000000000 : ℝ), (11600491560991/25000000000000 : ℝ), (21778743770811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1624626577/10000000000 : ℝ)|^4891 ≤ (2510136551461/25000000000000 : ℝ)^3867
        have hw : |(-1624626577/10000000000 : ℝ)|=(1624626577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724718941/5000000000 : ℝ)|^4891 ≤ (11600491560991/25000000000000 : ℝ)^3867
        have hw : |(2724718941/5000000000 : ℝ)|=(2724718941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183583783/10000000000 : ℝ)|^4891 ≤ (21778743770811/50000000000000 : ℝ)^3867
        have hw : |(5183583783/10000000000 : ℝ)|=(5183583783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s4_1 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674373309/5000000000 : ℝ)*x 0 + (-1761519153/10000000000 : ℝ)*x 1 + (1036716819/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674373309/5000000000 : ℝ)^4891 ≤ (22660102623933/50000000000000 : ℝ)^3867 := by
    have hnat : (2674373309 : ℕ)^4891*50000000000000^3867 ≤ 22660102623933^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674373309 5000000000 22660102623933 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1761519153/10000000000 : ℝ)^4891 ≤ (1112230388823/10000000000000 : ℝ)^3867 := by
    have hnat : (1761519153 : ℕ)^4891*10000000000000^3867 ≤ 1112230388823^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761519153 10000000000 1112230388823 10000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036716819/2000000000 : ℝ)^4891 ≤ (21778745428797/50000000000000 : ℝ)^3867 := by
    have hnat : (1036716819 : ℕ)^4891*50000000000000^3867 ≤ 21778745428797^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036716819 2000000000 21778745428797 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674373309/5000000000 : ℝ), (-1761519153/10000000000 : ℝ), (1036716819/2000000000 : ℝ)] ![(22660102623933/50000000000000 : ℝ), (1112230388823/10000000000000 : ℝ), (21778745428797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674373309/5000000000 : ℝ)|^4891 ≤ (22660102623933/50000000000000 : ℝ)^3867
        have hw : |(2674373309/5000000000 : ℝ)|=(2674373309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1761519153/10000000000 : ℝ)|^4891 ≤ (1112230388823/10000000000000 : ℝ)^3867
        have hw : |(-1761519153/10000000000 : ℝ)|=(1761519153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036716819/2000000000 : ℝ)|^4891 ≤ (21778745428797/50000000000000 : ℝ)^3867
        have hw : |(1036716819/2000000000 : ℝ)|=(1036716819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s4_2 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267437333/500000000 : ℝ)*x 0 + (259179193/500000000 : ℝ)*x 1 + (-110094963/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267437333/500000000 : ℝ)^4891 ≤ (4532020569797/10000000000000 : ℝ)^3867 := by
    have hnat : (267437333 : ℕ)^4891*10000000000000^3867 ≤ 4532020569797^3867*500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267437333 500000000 4532020569797 10000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259179193/500000000 : ℝ)^4891 ≤ (43557488359987/100000000000000 : ℝ)^3867 := by
    have hnat : (259179193 : ℕ)^4891*100000000000000^3867 ≤ 43557488359987^3867*500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259179193 500000000 43557488359987 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110094963/625000000 : ℝ)^4891 ≤ (11122305924667/100000000000000 : ℝ)^3867 := by
    have hnat : (110094963 : ℕ)^4891*100000000000000^3867 ≤ 11122305924667^3867*625000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110094963 625000000 11122305924667 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267437333/500000000 : ℝ), (259179193/500000000 : ℝ), (-110094963/625000000 : ℝ)] ![(4532020569797/10000000000000 : ℝ), (43557488359987/100000000000000 : ℝ), (11122305924667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267437333/500000000 : ℝ)|^4891 ≤ (4532020569797/10000000000000 : ℝ)^3867
        have hw : |(267437333/500000000 : ℝ)|=(267437333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259179193/500000000 : ℝ)|^4891 ≤ (43557488359987/100000000000000 : ℝ)^3867
        have hw : |(259179193/500000000 : ℝ)|=(259179193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110094963/625000000 : ℝ)|^4891 ≤ (11122305924667/100000000000000 : ℝ)^3867
        have hw : |(-110094963/625000000 : ℝ)|=(110094963/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s4_3 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4186148189/10000000000 : ℝ)*x 0 + (481929141/1250000000 : ℝ)*x 1 + (1134300907/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186148189/10000000000 : ℝ)^4891 ≤ (33240634447817/100000000000000 : ℝ)^3867 := by
    have hnat : (4186148189 : ℕ)^4891*100000000000000^3867 ≤ 33240634447817^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186148189 10000000000 33240634447817 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481929141/1250000000 : ℝ)^4891 ≤ (14977295077701/50000000000000 : ℝ)^3867 := by
    have hnat : (481929141 : ℕ)^4891*50000000000000^3867 ≤ 14977295077701^3867*1250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481929141 1250000000 14977295077701 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134300907/2500000000 : ℝ)^4891 ≤ (9201193847281/25000000000000 : ℝ)^3867 := by
    have hnat : (1134300907 : ℕ)^4891*25000000000000^3867 ≤ 9201193847281^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134300907 2500000000 9201193847281 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186148189/10000000000 : ℝ), (481929141/1250000000 : ℝ), (1134300907/2500000000 : ℝ)] ![(33240634447817/100000000000000 : ℝ), (14977295077701/50000000000000 : ℝ), (9201193847281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186148189/10000000000 : ℝ)|^4891 ≤ (33240634447817/100000000000000 : ℝ)^3867
        have hw : |(4186148189/10000000000 : ℝ)|=(4186148189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(481929141/1250000000 : ℝ)|^4891 ≤ (14977295077701/50000000000000 : ℝ)^3867
        have hw : |(481929141/1250000000 : ℝ)|=(481929141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134300907/2500000000 : ℝ)|^4891 ≤ (9201193847281/25000000000000 : ℝ)^3867
        have hw : |(1134300907/2500000000 : ℝ)|=(1134300907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s4_4 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1624691539/10000000000 : ℝ)*x 0 + (1037117469/2000000000 : ℝ)*x 1 + (544741333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1624691539/10000000000 : ℝ)^4891 ≤ (10041054001479/100000000000000 : ℝ)^3867 := by
    have hnat : (1624691539 : ℕ)^4891*100000000000000^3867 ≤ 10041054001479^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624691539 10000000000 10041054001479 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037117469/2000000000 : ℝ)^4891 ≤ (43578782715887/100000000000000 : ℝ)^3867 := by
    have hnat : (1037117469 : ℕ)^4891*100000000000000^3867 ≤ 43578782715887^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037117469 2000000000 43578782715887 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544741333/1000000000 : ℝ)^4891 ≤ (9276032653973/20000000000000 : ℝ)^3867 := by
    have hnat : (544741333 : ℕ)^4891*20000000000000^3867 ≤ 9276032653973^3867*1000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544741333 1000000000 9276032653973 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1624691539/10000000000 : ℝ), (1037117469/2000000000 : ℝ), (544741333/1000000000 : ℝ)] ![(10041054001479/100000000000000 : ℝ), (43578782715887/100000000000000 : ℝ), (9276032653973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1624691539/10000000000 : ℝ)|^4891 ≤ (10041054001479/100000000000000 : ℝ)^3867
        have hw : |(-1624691539/10000000000 : ℝ)|=(1624691539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037117469/2000000000 : ℝ)|^4891 ≤ (43578782715887/100000000000000 : ℝ)^3867
        have hw : |(1037117469/2000000000 : ℝ)|=(1037117469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544741333/1000000000 : ℝ)|^4891 ≤ (9276032653973/20000000000000 : ℝ)^3867
        have hw : |(544741333/1000000000 : ℝ)|=(544741333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s4_5 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638892069/5000000000 : ℝ)*x 0 + (-299537957/2000000000 : ℝ)*x 1 + (544741333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638892069/5000000000 : ℝ)^4891 ≤ (11140264480009/25000000000000 : ℝ)^3867 := by
    have hnat : (2638892069 : ℕ)^4891*25000000000000^3867 ≤ 11140264480009^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638892069 5000000000 11140264480009 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299537957/2000000000 : ℝ)^4891 ≤ (9058778793499/100000000000000 : ℝ)^3867 := by
    have hnat : (299537957 : ℕ)^4891*100000000000000^3867 ≤ 9058778793499^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299537957 2000000000 9058778793499 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544741333/1000000000 : ℝ)^4891 ≤ (9276032653973/20000000000000 : ℝ)^3867 := by
    have hnat : (544741333 : ℕ)^4891*20000000000000^3867 ≤ 9276032653973^3867*1000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544741333 1000000000 9276032653973 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638892069/5000000000 : ℝ), (-299537957/2000000000 : ℝ), (544741333/1000000000 : ℝ)] ![(11140264480009/25000000000000 : ℝ), (9058778793499/100000000000000 : ℝ), (9276032653973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638892069/5000000000 : ℝ)|^4891 ≤ (11140264480009/25000000000000 : ℝ)^3867
        have hw : |(2638892069/5000000000 : ℝ)|=(2638892069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299537957/2000000000 : ℝ)|^4891 ≤ (9058778793499/100000000000000 : ℝ)^3867
        have hw : |(-299537957/2000000000 : ℝ)|=(299537957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544741333/1000000000 : ℝ)|^4891 ≤ (9276032653973/20000000000000 : ℝ)^3867
        have hw : |(544741333/1000000000 : ℝ)|=(544741333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s4_6 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638892069/5000000000 : ℝ)*x 0 + (544741333/1000000000 : ℝ)*x 1 + (-299537957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638892069/5000000000 : ℝ)^4891 ≤ (11140264480009/25000000000000 : ℝ)^3867 := by
    have hnat : (2638892069 : ℕ)^4891*25000000000000^3867 ≤ 11140264480009^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638892069 5000000000 11140264480009 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544741333/1000000000 : ℝ)^4891 ≤ (9276032653973/20000000000000 : ℝ)^3867 := by
    have hnat : (544741333 : ℕ)^4891*20000000000000^3867 ≤ 9276032653973^3867*1000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544741333 1000000000 9276032653973 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299537957/2000000000 : ℝ)^4891 ≤ (9058778793499/100000000000000 : ℝ)^3867 := by
    have hnat : (299537957 : ℕ)^4891*100000000000000^3867 ≤ 9058778793499^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299537957 2000000000 9058778793499 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638892069/5000000000 : ℝ), (544741333/1000000000 : ℝ), (-299537957/2000000000 : ℝ)] ![(11140264480009/25000000000000 : ℝ), (9276032653973/20000000000000 : ℝ), (9058778793499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638892069/5000000000 : ℝ)|^4891 ≤ (11140264480009/25000000000000 : ℝ)^3867
        have hw : |(2638892069/5000000000 : ℝ)|=(2638892069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544741333/1000000000 : ℝ)|^4891 ≤ (9276032653973/20000000000000 : ℝ)^3867
        have hw : |(544741333/1000000000 : ℝ)|=(544741333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-299537957/2000000000 : ℝ)|^4891 ≤ (9058778793499/100000000000000 : ℝ)^3867
        have hw : |(-299537957/2000000000 : ℝ)|=(299537957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s4_7 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4186315199/10000000000 : ℝ)*x 0 + (2266032541/5000000000 : ℝ)*x 1 + (193031283/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186315199/10000000000 : ℝ)^4891 ≤ (8310577948753/25000000000000 : ℝ)^3867 := by
    have hnat : (4186315199 : ℕ)^4891*25000000000000^3867 ≤ 8310577948753^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186315199 10000000000 8310577948753 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266032541/5000000000 : ℝ)^4891 ≤ (1837603139111/5000000000000 : ℝ)^3867 := by
    have hnat : (2266032541 : ℕ)^4891*5000000000000^3867 ≤ 1837603139111^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266032541 5000000000 1837603139111 5000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193031283/500000000 : ℝ)^4891 ≤ (30005625410599/100000000000000 : ℝ)^3867 := by
    have hnat : (193031283 : ℕ)^4891*100000000000000^3867 ≤ 30005625410599^3867*500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193031283 500000000 30005625410599 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186315199/10000000000 : ℝ), (2266032541/5000000000 : ℝ), (193031283/500000000 : ℝ)] ![(8310577948753/25000000000000 : ℝ), (1837603139111/5000000000000 : ℝ), (30005625410599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186315199/10000000000 : ℝ)|^4891 ≤ (8310577948753/25000000000000 : ℝ)^3867
        have hw : |(4186315199/10000000000 : ℝ)|=(4186315199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2266032541/5000000000 : ℝ)|^4891 ≤ (1837603139111/5000000000000 : ℝ)^3867
        have hw : |(2266032541/5000000000 : ℝ)|=(2266032541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(193031283/500000000 : ℝ)|^4891 ≤ (30005625410599/100000000000000 : ℝ)^3867
        have hw : |(193031283/500000000 : ℝ)|=(193031283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1643_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2657/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10633/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8141/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16287/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2657/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16287/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2657/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16287/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2657/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16287/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2657/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16287/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2657/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16287/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2657/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2657/25000 : ℝ) ^ (4887/1024 : ℝ) ≤ (225828126340329/10000000000000000000 : ℝ) := by
    have hpowers : (2657/25000 : ℝ)^4887 ≤ (225828126340329/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2657 : ℕ)^4887*10000000000000000000^1024 ≤ 225828126340329^1024*25000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2657 25000 225828126340329 10000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2657/25000 : ℝ)) (X := (225828126340329/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16287/100000 : ℝ) ^ (4887/1024 : ℝ) ≤ (8659890971180517/50000000000000000000 : ℝ) := by
    have hpowers : (16287/100000 : ℝ)^4887 ≤ (8659890971180517/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16287 : ℕ)^4887*50000000000000000000^1024 ≤ 8659890971180517^1024*100000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16287 100000 8659890971180517 50000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16287/100000 : ℝ)) (X := (8659890971180517/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000225828126340329/5000000000000000000 : ℝ) ≤ (2500023659082617/2500000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (5000225828126340329/5000000000000000000 : ℝ)^1024 ≤ (2500023659082617/2500000000000000 : ℝ)^4887 := by
      have hnat : (5000225828126340329 : ℕ)^1024*2500000000000000^4887 ≤ 2500023659082617^4887*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000225828126340329 5000000000000000000 2500023659082617 2500000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500023659082617/2500000000000000 : ℝ)) (X := (5000225828126340329/5000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004894515801441081/25000000000000000000 : ℝ) ≤ (10000410198191493/10000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (25004894515801441081/25000000000000000000 : ℝ)^1024 ≤ (10000410198191493/10000000000000000 : ℝ)^4887 := by
      have hnat : (25004894515801441081 : ℕ)^1024*10000000000000000^4887 ≤ 10000410198191493^4887*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004894515801441081 25000000000000000000 10000410198191493 10000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000410198191493/10000000000000000 : ℝ)) (X := (25004894515801441081/25000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008659890971180517/25000000000000000000 : ℝ) ≤ (5000362880026259/5000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (25008659890971180517/25000000000000000000 : ℝ)^1024 ≤ (5000362880026259/5000000000000000 : ℝ)^4887 := by
      have hnat : (25008659890971180517 : ℕ)^1024*5000000000000000^4887 ≤ 5000362880026259^4887*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008659890971180517 25000000000000000000 5000362880026259 5000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000362880026259/5000000000000000 : ℝ)) (X := (25008659890971180517/25000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(225828126340329/10000000000000000000 : ℝ) ≤ ((14145956991019042753/14147500000000000000 : ℝ)+2*(12622474441/22636000000000 : ℝ)*(2657/25000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (14145956991019042753/14147500000000000000 : ℝ)+2*(12622474441/22636000000000 : ℝ)*(2657/25000 : ℝ)=(2500023659082617/2500000000000000 : ℝ) by norm_num, show 1+2*(225828126340329/10000000000000000000 : ℝ)=(5000225828126340329/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8659890971180517/50000000000000000000 : ℝ)+(225828126340329/10000000000000000000 : ℝ) ≤ ((14145956991019042753/14147500000000000000 : ℝ)+(12622474441/22636000000000 : ℝ)*((16287/100000 : ℝ)+(2657/25000 : ℝ)))^(4887/1024 : ℝ) := by
    rw [show (14145956991019042753/14147500000000000000 : ℝ)+(12622474441/22636000000000 : ℝ)*((16287/100000 : ℝ)+(2657/25000 : ℝ))=(10000410198191493/10000000000000000 : ℝ) by norm_num, show 1+(8659890971180517/50000000000000000000 : ℝ)+(225828126340329/10000000000000000000 : ℝ)=(25004894515801441081/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8659890971180517/50000000000000000000 : ℝ) ≤ ((14145956991019042753/14147500000000000000 : ℝ)+2*(12622474441/22636000000000 : ℝ)*(16287/100000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (14145956991019042753/14147500000000000000 : ℝ)+2*(12622474441/22636000000000 : ℝ)*(16287/100000 : ℝ)=(5000362880026259/5000000000000000 : ℝ) by norm_num, show 1+2*(8659890971180517/50000000000000000000 : ℝ)=(25008659890971180517/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14145956991019042753/14147500000000000000 : ℝ)*(X 1 0+X 2 0)+(12622474441/22636000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (2657/25000 : ℝ)) (hi := (16287/100000 : ℝ)) (c := (14145956991019042753/14147500000000000000 : ℝ)) (alpha := (12622474441/22636000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14145956991019042753/14147500000000000000 : ℝ)*(X 0 1+X 2 1)+(12622474441/22636000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (2657/25000 : ℝ)) (hi := (16287/100000 : ℝ)) (c := (14145956991019042753/14147500000000000000 : ℝ)) (alpha := (12622474441/22636000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14145956991019042753/14147500000000000000 : ℝ)*(X 0 2+X 1 2)+(12622474441/22636000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (2657/25000 : ℝ)) (hi := (16287/100000 : ℝ)) (c := (14145956991019042753/14147500000000000000 : ℝ)) (alpha := (12622474441/22636000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1624626577/10000000000 : ℝ)*X 0 0+(2724718941/5000000000 : ℝ)*X 0 1+(5183583783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674373309/5000000000 : ℝ)*X 1 0+(-1761519153/10000000000 : ℝ)*X 1 1+(1036716819/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267437333/500000000 : ℝ)*X 2 0+(259179193/500000000 : ℝ)*X 2 1+(-110094963/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4186148189/10000000000 : ℝ)*X 0 0+(481929141/1250000000 : ℝ)*X 0 1+(1134300907/2500000000 : ℝ)*X 0 2+(4186148189/10000000000 : ℝ)*X 1 0+(481929141/1250000000 : ℝ)*X 1 1+(1134300907/2500000000 : ℝ)*X 1 2+(4186148189/10000000000 : ℝ)*X 2 0+(481929141/1250000000 : ℝ)*X 2 1+(1134300907/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1624691539/10000000000 : ℝ)*X 0 0+(1037117469/2000000000 : ℝ)*X 0 1+(544741333/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638892069/5000000000 : ℝ)*X 1 0+(-299537957/2000000000 : ℝ)*X 1 1+(544741333/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638892069/5000000000 : ℝ)*X 2 0+(544741333/1000000000 : ℝ)*X 2 1+(-299537957/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4186315199/10000000000 : ℝ)*X 0 0+(2266032541/5000000000 : ℝ)*X 0 1+(193031283/500000000 : ℝ)*X 0 2+(4186315199/10000000000 : ℝ)*X 1 0+(2266032541/5000000000 : ℝ)*X 1 1+(193031283/500000000 : ℝ)*X 1 2+(4186315199/10000000000 : ℝ)*X 2 0+(2266032541/5000000000 : ℝ)*X 2 1+(193031283/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1373022945087259366181853189/176843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1107858861/100000000000000 : ℝ)*(base19) + (1101823523/100000000000000 : ℝ)*(base23) + (290886933/100000000000000 : ℝ)*(upper3) + (9513209/50000000000000 : ℝ)*(upper4) + (69673611/100000000000000 : ℝ)*(upper5) + (1307069563013479/50000000000000 : ℝ)*(major0) + (1307069563013479/50000000000000 : ℝ)*(major1) + (1307069563013479/50000000000000 : ℝ)*(major2) + (3761479985289949/100000000000000 : ℝ)*(sp0) + (470186565622063/12500000000000 : ℝ)*(sp1) + (1880746265505921/50000000000000 : ℝ)*(sp2) + (733387912904983/50000000000000 : ℝ)*(sp3) + (1705943177/12500000000000 : ℝ)*(sp4) + (8534607059/100000000000000 : ℝ)*(sp7) + (733392180208513/50000000000000 : ℝ)*(f.failure) + (752298726567073/20000000000000 : ℝ)*(f.sum) + (290982285507/1414750000000000000000000000 : ℝ)*base65 + (1876442839038642687/707375000000000000000000000000000 : ℝ)*base67 + (455463050370017687/707375000000000000000000000000000 : ℝ)*base69 + (1947442942811517687/707375000000000000000000000000000 : ℝ)*base71 + (4763070902981/1414750000000000000000000000 : ℝ)*base73 + (2368904267214142687/707375000000000000000000000000000 : ℝ)*base75 + (1934367647882517687/707375000000000000000000000000000 : ℝ)*base77 + (460201822528607313/707375000000000000000000000000000 : ℝ)*base80 + (1347272095439/2829500000000000000000000000 : ℝ)*base82 + (59176441/5000000000000000000000 : ℝ)*base89 + (59176441/5000000000000000000000 : ℝ)*base91 + (59176441/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18731641642824179758947/1414750000000000000000000000 : ℝ) := by norm_num
    linear_combination (981330689/50000000000000 : ℝ)*(base19) + (530584009/25000000000000 : ℝ)*(base23) + (615896327/100000000000000 : ℝ)*(lower1) + (138811139/50000000000000 : ℝ)*(upper3) + (71930933/100000000000000 : ℝ)*(lower4) + (137133703/50000000000000 : ℝ)*(upper5) + (1327158640945507/50000000000000 : ℝ)*(major0) + (1327158640945507/50000000000000 : ℝ)*(major1) + (1327158640945507/50000000000000 : ℝ)*(major2) + (1739214287/100000000000000 : ℝ)*(sp2) + (1909652969340069/50000000000000 : ℝ)*(sp4) + (95482599400469/2500000000000 : ℝ)*(sp5) + (477412759641227/12500000000000 : ℝ)*(sp6) + (744664091880131/50000000000000 : ℝ)*(sp7) + (744664091880131/50000000000000 : ℝ)*(f.failure) + (1909652969340069/50000000000000 : ℝ)*(f.sum) + (13879361541667/2829500000000000000000000000 : ℝ)*base66 + (12766013368775114229/707375000000000000000000000000000 : ℝ)*base68 + (6865950786950635771/707375000000000000000000000000000 : ℝ)*base69 + (6916323406764614229/707375000000000000000000000000000 : ℝ)*base72 + (2242747113657/2829500000000000000000000000 : ℝ)*base73 + (22989409999408135771/707375000000000000000000000000000 : ℝ)*base75 + (52196676168885771/707375000000000000000000000000000 : ℝ)*base77 + (2422635697763864229/707375000000000000000000000000000 : ℝ)*base80 + (6112784438553/2829500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3698133/5000000000000000000000 : ℝ)*base90 + (3698133/5000000000000000000000 : ℝ)*base92 + (3698133/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1643_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2657/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10633/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8141/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1643_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1643_s5_0 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348749711/10000000000 : ℝ)*x 0 + (5183595311/10000000000 : ℝ)*x 1 + (-70460003/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348749711/10000000000 : ℝ)^4891 ≤ (22660119197397/50000000000000 : ℝ)^3867 := by
    have hnat : (5348749711 : ℕ)^4891*50000000000000^3867 ≤ 22660119197397^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348749711 10000000000 22660119197397 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183595311/10000000000 : ℝ)^4891 ≤ (5444701257819/12500000000000 : ℝ)^3867 := by
    have hnat : (5183595311 : ℕ)^4891*12500000000000^3867 ≤ 5444701257819^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183595311 10000000000 5444701257819 12500000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70460003/400000000 : ℝ)^4891 ≤ (2780537882747/25000000000000 : ℝ)^3867 := by
    have hnat : (70460003 : ℕ)^4891*25000000000000^3867 ≤ 2780537882747^3867*400000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70460003 400000000 2780537882747 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348749711/10000000000 : ℝ), (5183595311/10000000000 : ℝ), (-70460003/400000000 : ℝ)] ![(22660119197397/50000000000000 : ℝ), (5444701257819/12500000000000 : ℝ), (2780537882747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348749711/10000000000 : ℝ)|^4891 ≤ (22660119197397/50000000000000 : ℝ)^3867
        have hw : |(5348749711/10000000000 : ℝ)|=(5348749711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183595311/10000000000 : ℝ)|^4891 ≤ (5444701257819/12500000000000 : ℝ)^3867
        have hw : |(5183595311/10000000000 : ℝ)|=(5183595311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-70460003/400000000 : ℝ)|^4891 ≤ (2780537882747/25000000000000 : ℝ)^3867
        have hw : |(-70460003/400000000 : ℝ)|=(70460003/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s5_1 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-16246943/100000000 : ℝ)*x 0 + (5185601853/10000000000 : ℝ)*x 1 + (1089479401/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16246943/100000000 : ℝ)^4891 ≤ (10041075583811/100000000000000 : ℝ)^3867 := by
    have hnat : (16246943 : ℕ)^4891*100000000000000^3867 ≤ 10041075583811^3867*100000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16246943 100000000 10041075583811 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185601853/10000000000 : ℝ)^4891 ≤ (43578936924397/100000000000000 : ℝ)^3867 := by
    have hnat : (5185601853 : ℕ)^4891*100000000000000^3867 ≤ 43578936924397^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185601853 10000000000 43578936924397 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089479401/2000000000 : ℝ)^4891 ≤ (9275997494007/20000000000000 : ℝ)^3867 := by
    have hnat : (1089479401 : ℕ)^4891*20000000000000^3867 ≤ 9275997494007^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089479401 2000000000 9275997494007 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16246943/100000000 : ℝ), (5185601853/10000000000 : ℝ), (1089479401/2000000000 : ℝ)] ![(10041075583811/100000000000000 : ℝ), (43578936924397/100000000000000 : ℝ), (9275997494007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16246943/100000000 : ℝ)|^4891 ≤ (10041075583811/100000000000000 : ℝ)^3867
        have hw : |(-16246943/100000000 : ℝ)|=(16246943/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185601853/10000000000 : ℝ)|^4891 ≤ (43578936924397/100000000000000 : ℝ)^3867
        have hw : |(5185601853/10000000000 : ℝ)|=(5185601853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089479401/2000000000 : ℝ)|^4891 ≤ (9275997494007/20000000000000 : ℝ)^3867
        have hw : |(1089479401/2000000000 : ℝ)|=(1089479401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s5_2 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319447037/2500000000 : ℝ)*x 0 + (-1497707017/10000000000 : ℝ)*x 1 + (680924639/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319447037/2500000000 : ℝ)^4891 ≤ (44561100742513/100000000000000 : ℝ)^3867 := by
    have hnat : (1319447037 : ℕ)^4891*100000000000000^3867 ≤ 44561100742513^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319447037 2500000000 44561100742513 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1497707017/10000000000 : ℝ)^4891 ≤ (9058910621487/100000000000000 : ℝ)^3867 := by
    have hnat : (1497707017 : ℕ)^4891*100000000000000^3867 ≤ 9058910621487^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1497707017 10000000000 9058910621487 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680924639/1250000000 : ℝ)^4891 ≤ (4637998862229/10000000000000 : ℝ)^3867 := by
    have hnat : (680924639 : ℕ)^4891*10000000000000^3867 ≤ 4637998862229^3867*1250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680924639 1250000000 4637998862229 10000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319447037/2500000000 : ℝ), (-1497707017/10000000000 : ℝ), (680924639/1250000000 : ℝ)] ![(44561100742513/100000000000000 : ℝ), (9058910621487/100000000000000 : ℝ), (4637998862229/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319447037/2500000000 : ℝ)|^4891 ≤ (44561100742513/100000000000000 : ℝ)^3867
        have hw : |(1319447037/2500000000 : ℝ)|=(1319447037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1497707017/10000000000 : ℝ)|^4891 ≤ (9058910621487/100000000000000 : ℝ)^3867
        have hw : |(-1497707017/10000000000 : ℝ)|=(1497707017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680924639/1250000000 : ℝ)|^4891 ≤ (4637998862229/10000000000000 : ℝ)^3867
        have hw : |(680924639/1250000000 : ℝ)|=(680924639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s5_3 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277788351/10000000000 : ℝ)*x 0 + (2723698433/5000000000 : ℝ)*x 1 + (-37442677/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277788351/10000000000 : ℝ)^4891 ≤ (22280551455167/50000000000000 : ℝ)^3867 := by
    have hnat : (5277788351 : ℕ)^4891*50000000000000^3867 ≤ 22280551455167^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277788351 10000000000 22280551455167 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723698433/5000000000 : ℝ)^4891 ≤ (46379985973179/100000000000000 : ℝ)^3867 := by
    have hnat : (2723698433 : ℕ)^4891*100000000000000^3867 ≤ 46379985973179^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723698433 5000000000 46379985973179 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37442677/250000000 : ℝ)^4891 ≤ (181178222069/2000000000000 : ℝ)^3867 := by
    have hnat : (37442677 : ℕ)^4891*2000000000000^3867 ≤ 181178222069^3867*250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37442677 250000000 181178222069 2000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277788351/10000000000 : ℝ), (2723698433/5000000000 : ℝ), (-37442677/250000000 : ℝ)] ![(22280551455167/50000000000000 : ℝ), (46379985973179/100000000000000 : ℝ), (181178222069/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277788351/10000000000 : ℝ)|^4891 ≤ (22280551455167/50000000000000 : ℝ)^3867
        have hw : |(5277788351/10000000000 : ℝ)|=(5277788351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723698433/5000000000 : ℝ)|^4891 ≤ (46379985973179/100000000000000 : ℝ)^3867
        have hw : |(2723698433/5000000000 : ℝ)|=(2723698433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37442677/250000000 : ℝ)|^4891 ≤ (181178222069/2000000000000 : ℝ)^3867
        have hw : |(-37442677/250000000 : ℝ)|=(37442677/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s5_4 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093158653/5000000000 : ℝ)*x 0 + (4532025459/10000000000 : ℝ)*x 1 + (241291553/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093158653/5000000000 : ℝ)^4891 ≤ (8310583239139/25000000000000 : ℝ)^3867 := by
    have hnat : (2093158653 : ℕ)^4891*25000000000000^3867 ≤ 8310583239139^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093158653 5000000000 8310583239139 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4532025459/10000000000 : ℝ)^4891 ≤ (18375828190069/50000000000000 : ℝ)^3867 := by
    have hnat : (4532025459 : ℕ)^4891*50000000000000^3867 ≤ 18375828190069^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532025459 10000000000 18375828190069 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241291553/625000000 : ℝ)^4891 ≤ (3000601064243/10000000000000 : ℝ)^3867 := by
    have hnat : (241291553 : ℕ)^4891*10000000000000^3867 ≤ 3000601064243^3867*625000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241291553 625000000 3000601064243 10000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093158653/5000000000 : ℝ), (4532025459/10000000000 : ℝ), (241291553/625000000 : ℝ)] ![(8310583239139/25000000000000 : ℝ), (18375828190069/50000000000000 : ℝ), (3000601064243/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093158653/5000000000 : ℝ)|^4891 ≤ (8310583239139/25000000000000 : ℝ)^3867
        have hw : |(2093158653/5000000000 : ℝ)|=(2093158653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4532025459/10000000000 : ℝ)|^4891 ≤ (18375828190069/50000000000000 : ℝ)^3867
        have hw : |(4532025459/10000000000 : ℝ)|=(4532025459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241291553/625000000 : ℝ)|^4891 ≤ (3000601064243/10000000000000 : ℝ)^3867
        have hw : |(241291553/625000000 : ℝ)|=(241291553/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1643_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8141/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10633/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10633/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16281/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8141/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10633/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8141/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10633/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8141/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10633/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8141/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10633/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8141/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10633/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8141/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10633/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10633/100000 : ℝ) ^ (4887/1024 : ℝ) ≤ (1131678062813723/50000000000000000000 : ℝ) := by
    have hpowers : (10633/100000 : ℝ)^4887 ≤ (1131678062813723/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10633 : ℕ)^4887*50000000000000000000^1024 ≤ 1131678062813723^1024*100000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10633 100000 1131678062813723 50000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10633/100000 : ℝ)) (X := (1131678062813723/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8141/50000 : ℝ) ^ (4887/1024 : ℝ) ≤ (4323605296144593/25000000000000000000 : ℝ) := by
    have hpowers : (8141/50000 : ℝ)^4887 ≤ (4323605296144593/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8141 : ℕ)^4887*25000000000000000000^1024 ≤ 4323605296144593^1024*50000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8141 50000 4323605296144593 25000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8141/50000 : ℝ)) (X := (4323605296144593/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001131678062813723/25000000000000000000 : ℝ) ≤ (2500023712248907/2500000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (25001131678062813723/25000000000000000000 : ℝ)^1024 ≤ (2500023712248907/2500000000000000 : ℝ)^4887 := by
      have hnat : (25001131678062813723 : ℕ)^1024*2500000000000000^4887 ≤ 2500023712248907^4887*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001131678062813723 25000000000000000000 2500023712248907 2500000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500023712248907/2500000000000000 : ℝ)) (X := (25001131678062813723/25000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50009778888655102909/50000000000000000000 : ℝ) ≤ (5000204886597849/5000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (50009778888655102909/50000000000000000000 : ℝ)^1024 ≤ (5000204886597849/5000000000000000 : ℝ)^4887 := by
      have hnat : (50009778888655102909 : ℕ)^1024*5000000000000000^4887 ≤ 5000204886597849^4887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009778888655102909 50000000000000000000 5000204886597849 5000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000204886597849/5000000000000000 : ℝ)) (X := (50009778888655102909/50000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504323605296144593/12500000000000000000 : ℝ) ≤ (1250090587174471/1250000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (12504323605296144593/12500000000000000000 : ℝ)^1024 ≤ (1250090587174471/1250000000000000 : ℝ)^4887 := by
      have hnat : (12504323605296144593 : ℕ)^1024*1250000000000000^4887 ≤ 1250090587174471^4887*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504323605296144593 12500000000000000000 1250090587174471 1250000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250090587174471/1250000000000000 : ℝ)) (X := (12504323605296144593/12500000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1131678062813723/50000000000000000000 : ℝ) ≤ ((63039998464216087/63046875000000000 : ℝ)+2*(31492420007/56490000000000 : ℝ)*(10633/100000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (63039998464216087/63046875000000000 : ℝ)+2*(31492420007/56490000000000 : ℝ)*(10633/100000 : ℝ)=(2500023712248907/2500000000000000 : ℝ) by norm_num, show 1+2*(1131678062813723/50000000000000000000 : ℝ)=(25001131678062813723/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4323605296144593/25000000000000000000 : ℝ)+(1131678062813723/50000000000000000000 : ℝ) ≤ ((63039998464216087/63046875000000000 : ℝ)+(31492420007/56490000000000 : ℝ)*((8141/50000 : ℝ)+(10633/100000 : ℝ)))^(4887/1024 : ℝ) := by
    rw [show (63039998464216087/63046875000000000 : ℝ)+(31492420007/56490000000000 : ℝ)*((8141/50000 : ℝ)+(10633/100000 : ℝ))=(5000204886597849/5000000000000000 : ℝ) by norm_num, show 1+(4323605296144593/25000000000000000000 : ℝ)+(1131678062813723/50000000000000000000 : ℝ)=(50009778888655102909/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4323605296144593/25000000000000000000 : ℝ) ≤ ((63039998464216087/63046875000000000 : ℝ)+2*(31492420007/56490000000000 : ℝ)*(8141/50000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (63039998464216087/63046875000000000 : ℝ)+2*(31492420007/56490000000000 : ℝ)*(8141/50000 : ℝ)=(1250090587174471/1250000000000000 : ℝ) by norm_num, show 1+2*(4323605296144593/25000000000000000000 : ℝ)=(12504323605296144593/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (63039998464216087/63046875000000000 : ℝ)*(X 1 0+X 2 0)+(31492420007/56490000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (10633/100000 : ℝ)) (hi := (8141/50000 : ℝ)) (c := (63039998464216087/63046875000000000 : ℝ)) (alpha := (31492420007/56490000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (63039998464216087/63046875000000000 : ℝ)*(X 0 1+X 2 1)+(31492420007/56490000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (10633/100000 : ℝ)) (hi := (8141/50000 : ℝ)) (c := (63039998464216087/63046875000000000 : ℝ)) (alpha := (31492420007/56490000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (63039998464216087/63046875000000000 : ℝ)*(X 0 2+X 1 2)+(31492420007/56490000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (10633/100000 : ℝ)) (hi := (8141/50000 : ℝ)) (c := (63039998464216087/63046875000000000 : ℝ)) (alpha := (31492420007/56490000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5348749711/10000000000 : ℝ)*X 2 0+(5183595311/10000000000 : ℝ)*X 2 1+(-70460003/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s5_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-16246943/100000000 : ℝ)*X 0 0+(5185601853/10000000000 : ℝ)*X 0 1+(1089479401/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s5_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1319447037/2500000000 : ℝ)*X 1 0+(-1497707017/10000000000 : ℝ)*X 1 1+(680924639/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s5_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5277788351/10000000000 : ℝ)*X 2 0+(2723698433/5000000000 : ℝ)*X 2 1+(-37442677/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s5_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2093158653/5000000000 : ℝ)*X 0 0+(4532025459/10000000000 : ℝ)*X 0 1+(241291553/625000000 : ℝ)*X 0 2+(2093158653/5000000000 : ℝ)*X 1 0+(4532025459/10000000000 : ℝ)*X 1 1+(241291553/625000000 : ℝ)*X 1 2+(2093158653/5000000000 : ℝ)*X 2 0+(4532025459/10000000000 : ℝ)*X 2 1+(241291553/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s5_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1112338511489457963951/188300000000000000000000000 : ℝ) := by norm_num
    linear_combination (788243607/100000000000000 : ℝ)*(base19) + (1031158759/100000000000000 : ℝ)*(base23) + (270322619/100000000000000 : ℝ)*(lower1) + (129404921/100000000000000 : ℝ)*(upper3) + (170373/390625000000 : ℝ)*(lower4) + (11979387/12500000000000 : ℝ)*(upper5) + (2654639062606017/100000000000000 : ℝ)*(major0) + (2654639062606017/100000000000000 : ℝ)*(major1) + (2654639062606017/100000000000000 : ℝ)*(major2) + (99331413/10000000000000 : ℝ)*(sp0) + (190988459725209/5000000000000 : ℝ)*(sp1) + (3819768406260573/100000000000000 : ℝ)*(sp2) + (3819767170031291/100000000000000 : ℝ)*(sp3) + (372377183449729/25000000000000 : ℝ)*(sp4) + (372377183449729/25000000000000 : ℝ)*(f.failure) + (190988459725209/5000000000000 : ℝ)*(f.sum) + (1292967190311/941500000000000000000000000 : ℝ)*base66 + (1290185089138132027/29421875000000000000000000000000 : ℝ)*base67 + (187564997720805473/29421875000000000000000000000000 : ℝ)*base70 + (1019916300990819527/29421875000000000000000000000000 : ℝ)*base71 + (1964532067997/1883000000000000000000000000 : ℝ)*base73 + (937460458528742973/29421875000000000000000000000000 : ℝ)*base76 + (90168033008995701/14710937500000000000000000000000 : ℝ)*base77 + (95853930286367973/29421875000000000000000000000000 : ℝ)*base80 + (3025295591727/470750000000000000000000000 : ℝ)*base82 + (13364153/2500000000000000000000 : ℝ)*base89 + (13364153/2500000000000000000000 : ℝ)*base91 + (13364153/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1643_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8141/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10633/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10633/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1643_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1643_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2111/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10633/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1643_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1643_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1643_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2111/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10633/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1643_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
