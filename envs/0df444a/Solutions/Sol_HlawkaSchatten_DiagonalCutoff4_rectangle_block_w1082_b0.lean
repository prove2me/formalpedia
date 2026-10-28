-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1082_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:50:15.724514+00:00
-- url     : https://prove2.me/submissions/dce02693-e12f-4ea7-bec8-0f904b1686f4

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
theorem support_rectangle_w1082_s0_0 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-23886839/125000000 : ℝ)*x 0 + (3034150791/5000000000 : ℝ)*x 1 + (59660469/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23886839/125000000 : ℝ)^8275 ≤ (443525207933/4000000000000 : ℝ)^6227 := by
    have hnat : (23886839 : ℕ)^8275*4000000000000^6227 ≤ 443525207933^6227*125000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23886839 125000000 443525207933 4000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3034150791/5000000000 : ℝ)^8275 ≤ (12872415607023/25000000000000 : ℝ)^6227 := by
    have hnat : (3034150791 : ℕ)^8275*25000000000000^6227 ≤ 12872415607023^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3034150791 5000000000 12872415607023 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59660469/125000000 : ℝ)^8275 ≤ (37422207360101/100000000000000 : ℝ)^6227 := by
    have hnat : (59660469 : ℕ)^8275*100000000000000^6227 ≤ 37422207360101^6227*125000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59660469 125000000 37422207360101 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23886839/125000000 : ℝ), (3034150791/5000000000 : ℝ), (59660469/125000000 : ℝ)] ![(443525207933/4000000000000 : ℝ), (12872415607023/25000000000000 : ℝ), (37422207360101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23886839/125000000 : ℝ)|^8275 ≤ (443525207933/4000000000000 : ℝ)^6227
        have hw : |(-23886839/125000000 : ℝ)|=(23886839/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3034150791/5000000000 : ℝ)|^8275 ≤ (12872415607023/25000000000000 : ℝ)^6227
        have hw : |(3034150791/5000000000 : ℝ)|=(3034150791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(59660469/125000000 : ℝ)|^8275 ≤ (37422207360101/100000000000000 : ℝ)^6227
        have hw : |(59660469/125000000 : ℝ)|=(59660469/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s0_1 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5520172847/10000000000 : ℝ)*x 0 + (-1328074001/5000000000 : ℝ)*x 1 + (4772837883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520172847/10000000000 : ℝ)^8275 ≤ (11350720227947/25000000000000 : ℝ)^6227 := by
    have hnat : (5520172847 : ℕ)^8275*25000000000000^6227 ≤ 11350720227947^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520172847 10000000000 11350720227947 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1328074001/5000000000 : ℝ)^8275 ≤ (343498158589/2000000000000 : ℝ)^6227 := by
    have hnat : (1328074001 : ℕ)^8275*2000000000000^6227 ≤ 343498158589^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328074001 5000000000 343498158589 2000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4772837883/10000000000 : ℝ)^8275 ≤ (584722049099/1562500000000 : ℝ)^6227 := by
    have hnat : (4772837883 : ℕ)^8275*1562500000000^6227 ≤ 584722049099^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772837883 10000000000 584722049099 1562500000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520172847/10000000000 : ℝ), (-1328074001/5000000000 : ℝ), (4772837883/10000000000 : ℝ)] ![(11350720227947/25000000000000 : ℝ), (343498158589/2000000000000 : ℝ), (584722049099/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520172847/10000000000 : ℝ)|^8275 ≤ (11350720227947/25000000000000 : ℝ)^6227
        have hw : |(5520172847/10000000000 : ℝ)|=(5520172847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1328074001/5000000000 : ℝ)|^8275 ≤ (343498158589/2000000000000 : ℝ)^6227
        have hw : |(-1328074001/5000000000 : ℝ)|=(1328074001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4772837883/10000000000 : ℝ)|^8275 ≤ (584722049099/1562500000000 : ℝ)^6227
        have hw : |(4772837883/10000000000 : ℝ)|=(4772837883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s0_2 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1104034503/2000000000 : ℝ)*x 0 + (2386418771/5000000000 : ℝ)*x 1 + (-1328074419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104034503/2000000000 : ℝ)^8275 ≤ (45402877283031/100000000000000 : ℝ)^6227 := by
    have hnat : (1104034503 : ℕ)^8275*100000000000000^6227 ≤ 45402877283031^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104034503 2000000000 45402877283031 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2386418771/5000000000 : ℝ)^8275 ≤ (37422207589327/100000000000000 : ℝ)^6227 := by
    have hnat : (2386418771 : ℕ)^8275*100000000000000^6227 ≤ 37422207589327^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386418771 5000000000 37422207589327 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1328074419/5000000000 : ℝ)^8275 ≤ (686996604519/4000000000000 : ℝ)^6227 := by
    have hnat : (1328074419 : ℕ)^8275*4000000000000^6227 ≤ 686996604519^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328074419 5000000000 686996604519 4000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1104034503/2000000000 : ℝ), (2386418771/5000000000 : ℝ), (-1328074419/5000000000 : ℝ)] ![(45402877283031/100000000000000 : ℝ), (37422207589327/100000000000000 : ℝ), (686996604519/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1104034503/2000000000 : ℝ)|^8275 ≤ (45402877283031/100000000000000 : ℝ)^6227
        have hw : |(1104034503/2000000000 : ℝ)|=(1104034503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2386418771/5000000000 : ℝ)|^8275 ≤ (37422207589327/100000000000000 : ℝ)^6227
        have hw : |(2386418771/5000000000 : ℝ)|=(2386418771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1328074419/5000000000 : ℝ)|^8275 ≤ (686996604519/4000000000000 : ℝ)^6227
        have hw : |(-1328074419/5000000000 : ℝ)|=(1328074419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s0_3 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4205888069/10000000000 : ℝ)*x 0 + (781005683/2500000000 : ℝ)*x 1 + (5671022243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205888069/10000000000 : ℝ)^8275 ≤ (31633566155567/100000000000000 : ℝ)^6227 := by
    have hnat : (4205888069 : ℕ)^8275*100000000000000^6227 ≤ 31633566155567^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205888069 10000000000 31633566155567 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781005683/2500000000 : ℝ)^8275 ≤ (21307405644699/100000000000000 : ℝ)^6227 := by
    have hnat : (781005683 : ℕ)^8275*100000000000000^6227 ≤ 21307405644699^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781005683 2500000000 21307405644699 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5671022243/10000000000 : ℝ)^8275 ≤ (47059028191149/100000000000000 : ℝ)^6227 := by
    have hnat : (5671022243 : ℕ)^8275*100000000000000^6227 ≤ 47059028191149^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671022243 10000000000 47059028191149 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205888069/10000000000 : ℝ), (781005683/2500000000 : ℝ), (5671022243/10000000000 : ℝ)] ![(31633566155567/100000000000000 : ℝ), (21307405644699/100000000000000 : ℝ), (47059028191149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205888069/10000000000 : ℝ)|^8275 ≤ (31633566155567/100000000000000 : ℝ)^6227
        have hw : |(4205888069/10000000000 : ℝ)|=(4205888069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(781005683/2500000000 : ℝ)|^8275 ≤ (21307405644699/100000000000000 : ℝ)^6227
        have hw : |(781005683/2500000000 : ℝ)|=(781005683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5671022243/10000000000 : ℝ)|^8275 ≤ (47059028191149/100000000000000 : ℝ)^6227
        have hw : |(5671022243/10000000000 : ℝ)|=(5671022243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s0_4 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-479067949/2500000000 : ℝ)*x 0 + (4806281469/10000000000 : ℝ)*x 1 + (6033686409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (479067949/2500000000 : ℝ)^8275 ≤ (5564603224709/50000000000000 : ℝ)^6227 := by
    have hnat : (479067949 : ℕ)^8275*50000000000000^6227 ≤ 5564603224709^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479067949 2500000000 5564603224709 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4806281469/10000000000 : ℝ)^8275 ≤ (37771073487291/100000000000000 : ℝ)^6227 := by
    have hnat : (4806281469 : ℕ)^8275*100000000000000^6227 ≤ 37771073487291^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4806281469 10000000000 37771073487291 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6033686409/10000000000 : ℝ)^8275 ≤ (51099720051683/100000000000000 : ℝ)^6227 := by
    have hnat : (6033686409 : ℕ)^8275*100000000000000^6227 ≤ 51099720051683^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6033686409 10000000000 51099720051683 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-479067949/2500000000 : ℝ), (4806281469/10000000000 : ℝ), (6033686409/10000000000 : ℝ)] ![(5564603224709/50000000000000 : ℝ), (37771073487291/100000000000000 : ℝ), (51099720051683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-479067949/2500000000 : ℝ)|^8275 ≤ (5564603224709/50000000000000 : ℝ)^6227
        have hw : |(-479067949/2500000000 : ℝ)|=(479067949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4806281469/10000000000 : ℝ)|^8275 ≤ (37771073487291/100000000000000 : ℝ)^6227
        have hw : |(4806281469/10000000000 : ℝ)|=(4806281469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6033686409/10000000000 : ℝ)|^8275 ≤ (51099720051683/100000000000000 : ℝ)^6227
        have hw : |(6033686409/10000000000 : ℝ)|=(6033686409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s0_5 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1009468/1953125 : ℝ)*x 0 + (-279060629/2000000000 : ℝ)*x 1 + (6033684707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009468/1953125 : ℝ)^8275 ≤ (20799851263319/50000000000000 : ℝ)^6227 := by
    have hnat : (1009468 : ℕ)^8275*50000000000000^6227 ≤ 20799851263319^6227*1953125^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009468 1953125 20799851263319 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279060629/2000000000 : ℝ)^8275 ≤ (1460119312317/20000000000000 : ℝ)^6227 := by
    have hnat : (279060629 : ℕ)^8275*20000000000000^6227 ≤ 1460119312317^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279060629 2000000000 1460119312317 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6033684707/10000000000 : ℝ)^8275 ≤ (51099700896581/100000000000000 : ℝ)^6227 := by
    have hnat : (6033684707 : ℕ)^8275*100000000000000^6227 ≤ 51099700896581^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6033684707 10000000000 51099700896581 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1009468/1953125 : ℝ), (-279060629/2000000000 : ℝ), (6033684707/10000000000 : ℝ)] ![(20799851263319/50000000000000 : ℝ), (1460119312317/20000000000000 : ℝ), (51099700896581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1009468/1953125 : ℝ)|^8275 ≤ (20799851263319/50000000000000 : ℝ)^6227
        have hw : |(1009468/1953125 : ℝ)|=(1009468/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279060629/2000000000 : ℝ)|^8275 ≤ (1460119312317/20000000000000 : ℝ)^6227
        have hw : |(-279060629/2000000000 : ℝ)|=(279060629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6033684707/10000000000 : ℝ)|^8275 ≤ (51099700896581/100000000000000 : ℝ)^6227
        have hw : |(6033684707/10000000000 : ℝ)|=(6033684707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s0_6 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1292119037/2500000000 : ℝ)*x 0 + (6033686139/10000000000 : ℝ)*x 1 + (-348825211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292119037/2500000000 : ℝ)^8275 ≤ (41599702398287/100000000000000 : ℝ)^6227 := by
    have hnat : (1292119037 : ℕ)^8275*100000000000000^6227 ≤ 41599702398287^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292119037 2500000000 41599702398287 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6033686139/10000000000 : ℝ)^8275 ≤ (51099717012977/100000000000000 : ℝ)^6227 := by
    have hnat : (6033686139 : ℕ)^8275*100000000000000^6227 ≤ 51099717012977^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6033686139 10000000000 51099717012977 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (348825211/2500000000 : ℝ)^8275 ≤ (7300580562491/100000000000000 : ℝ)^6227 := by
    have hnat : (348825211 : ℕ)^8275*100000000000000^6227 ≤ 7300580562491^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348825211 2500000000 7300580562491 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292119037/2500000000 : ℝ), (6033686139/10000000000 : ℝ), (-348825211/2500000000 : ℝ)] ![(41599702398287/100000000000000 : ℝ), (51099717012977/100000000000000 : ℝ), (7300580562491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292119037/2500000000 : ℝ)|^8275 ≤ (41599702398287/100000000000000 : ℝ)^6227
        have hw : |(1292119037/2500000000 : ℝ)|=(1292119037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6033686139/10000000000 : ℝ)|^8275 ≤ (51099717012977/100000000000000 : ℝ)^6227
        have hw : |(6033686139/10000000000 : ℝ)|=(6033686139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-348825211/2500000000 : ℝ)|^8275 ≤ (7300580562491/100000000000000 : ℝ)^6227
        have hw : |(-348825211/2500000000 : ℝ)|=(348825211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s0_7 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1054088883/2500000000 : ℝ)*x 0 + (350329059/625000000 : ℝ)*x 1 + (3192083027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054088883/2500000000 : ℝ)^8275 ≤ (31738230467101/100000000000000 : ℝ)^6227 := by
    have hnat : (1054088883 : ℕ)^8275*100000000000000^6227 ≤ 31738230467101^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054088883 2500000000 31738230467101 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350329059/625000000 : ℝ)^8275 ≤ (11583821603119/25000000000000 : ℝ)^6227 := by
    have hnat : (350329059 : ℕ)^8275*25000000000000^6227 ≤ 11583821603119^6227*625000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350329059 625000000 11583821603119 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3192083027/10000000000 : ℝ)^8275 ≤ (10963241555217/50000000000000 : ℝ)^6227 := by
    have hnat : (3192083027 : ℕ)^8275*50000000000000^6227 ≤ 10963241555217^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3192083027 10000000000 10963241555217 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054088883/2500000000 : ℝ), (350329059/625000000 : ℝ), (3192083027/10000000000 : ℝ)] ![(31738230467101/100000000000000 : ℝ), (11583821603119/25000000000000 : ℝ), (10963241555217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054088883/2500000000 : ℝ)|^8275 ≤ (31738230467101/100000000000000 : ℝ)^6227
        have hw : |(1054088883/2500000000 : ℝ)|=(1054088883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(350329059/625000000 : ℝ)|^8275 ≤ (11583821603119/25000000000000 : ℝ)^6227
        have hw : |(350329059/625000000 : ℝ)|=(350329059/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3192083027/10000000000 : ℝ)|^8275 ≤ (10963241555217/50000000000000 : ℝ)^6227
        have hw : |(3192083027/10000000000 : ℝ)|=(3192083027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1082_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (41/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28047/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4137/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4137 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4137*1^1024 ≤ 0^1024*1^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4137/1024 : ℝ) ≤ (123389108032645537/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4137 ≤ (123389108032645537/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4137*5000000000000000000^1024 ≤ 123389108032645537^1024*5^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 123389108032645537 5000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (123389108032645537/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4137 := by
      have hnat : (1 : ℕ)^1024*1^4137 ≤ 1^4137*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5123389108032645537/5000000000000000000 : ℝ) ≤ (314391375746407/312500000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (5123389108032645537/5000000000000000000 : ℝ)^1024 ≤ (314391375746407/312500000000000 : ℝ)^4137 := by
      have hnat : (5123389108032645537 : ℕ)^1024*312500000000000^4137 ≤ 314391375746407^4137*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5123389108032645537 5000000000000000000 314391375746407 312500000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314391375746407/312500000000000 : ℝ)) (X := (5123389108032645537/5000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2623389108032645537/2500000000000000000 : ℝ) ≤ (158141375746407/156250000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (2623389108032645537/2500000000000000000 : ℝ)^1024 ≤ (158141375746407/156250000000000 : ℝ)^4137 := by
      have hnat : (2623389108032645537 : ℕ)^1024*156250000000000^4137 ≤ 158141375746407^4137*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2623389108032645537 2500000000000000000 158141375746407 156250000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (158141375746407/156250000000000 : ℝ)) (X := (2623389108032645537/2500000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1891375746407/125000000000000 : ℝ)*(0 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1891375746407/125000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(123389108032645537/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1891375746407/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4137/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1891375746407/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(314391375746407/312500000000000 : ℝ) by norm_num, show 1+(123389108032645537/5000000000000000000 : ℝ)+(0 : ℝ)=(5123389108032645537/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(123389108032645537/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1891375746407/125000000000000 : ℝ)*(2/5 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1891375746407/125000000000000 : ℝ)*(2/5 : ℝ)=(158141375746407/156250000000000 : ℝ) by norm_num, show 1+2*(123389108032645537/5000000000000000000 : ℝ)=(2623389108032645537/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1891375746407/125000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1891375746407/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1891375746407/125000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1891375746407/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1891375746407/125000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1891375746407/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-23886839/125000000 : ℝ)*X 0 0+(3034150791/5000000000 : ℝ)*X 0 1+(59660469/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5520172847/10000000000 : ℝ)*X 1 0+(-1328074001/5000000000 : ℝ)*X 1 1+(4772837883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1104034503/2000000000 : ℝ)*X 2 0+(2386418771/5000000000 : ℝ)*X 2 1+(-1328074419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4205888069/10000000000 : ℝ)*X 0 0+(781005683/2500000000 : ℝ)*X 0 1+(5671022243/10000000000 : ℝ)*X 0 2+(4205888069/10000000000 : ℝ)*X 1 0+(781005683/2500000000 : ℝ)*X 1 1+(5671022243/10000000000 : ℝ)*X 1 2+(4205888069/10000000000 : ℝ)*X 2 0+(781005683/2500000000 : ℝ)*X 2 1+(5671022243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-479067949/2500000000 : ℝ)*X 0 0+(4806281469/10000000000 : ℝ)*X 0 1+(6033686409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1009468/1953125 : ℝ)*X 1 0+(-279060629/2000000000 : ℝ)*X 1 1+(6033684707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1292119037/2500000000 : ℝ)*X 2 0+(6033686139/10000000000 : ℝ)*X 2 1+(-348825211/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1054088883/2500000000 : ℝ)*X 0 0+(350329059/625000000 : ℝ)*X 0 1+(3192083027/10000000000 : ℝ)*X 0 2+(1054088883/2500000000 : ℝ)*X 1 0+(350329059/625000000 : ℝ)*X 1 1+(3192083027/10000000000 : ℝ)*X 1 2+(1054088883/2500000000 : ℝ)*X 2 0+(350329059/625000000 : ℝ)*X 2 1+(3192083027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5398312688197915093197/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (268383893/25000000000000 : ℝ)*(base19) + (523521067/50000000000000 : ℝ)*(base23) + (10723383/100000000000000 : ℝ)*(base24) + (31520149/100000000000000 : ℝ)*(base39) + (250100333/100000000000000 : ℝ)*(upper3) + (582277096636321/100000000000000 : ℝ)*(major0) + (582277096636321/100000000000000 : ℝ)*(major1) + (145569266279043/25000000000000 : ℝ)*(major2) + (48245524708377/6250000000000 : ℝ)*(sp0) + (385965005529883/50000000000000 : ℝ)*(sp1) + (771930058349969/100000000000000 : ℝ)*(sp2) + (196310260248807/50000000000000 : ℝ)*(sp3) + (1344630653/50000000000000 : ℝ)*(sp4) + (2441495529/100000000000000 : ℝ)*(sp7) + (196311480996571/50000000000000 : ℝ)*(f.failure) + (385965558057743/50000000000000 : ℝ)*(f.sum) + (26186811682349/12500000000000000000000000000 : ℝ)*base66 + (5256501982749/3125000000000000000000000000 : ℝ)*base68 + (129549414538853/12500000000000000000000000000 : ℝ)*base70 + (7852075838999/3125000000000000000000000000 : ℝ)*base72 + (29849798107349/12500000000000000000000000000 : ℝ)*base74 + (92269971838853/12500000000000000000000000000 : ℝ)*base76 + (25535671413853/12500000000000000000000000000 : ℝ)*base78 + (6773761326353/12500000000000000000000000000 : ℝ)*base80 + (44268526445103/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4220021/625000000000000000000 : ℝ)*base90 + (4220021/625000000000000000000 : ℝ)*base92 + (4220021/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11064032718455878297299/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (141599419/10000000000000 : ℝ)*(base19) + (82859933/5000000000000 : ℝ)*(base23) + (24575247/12500000000000 : ℝ)*(base39) + (296735539/100000000000000 : ℝ)*(base45) + (63113143/50000000000000 : ℝ)*(upper3) + (34530297/10000000000000 : ℝ)*(upper5) + (153639231716619/25000000000000 : ℝ)*(major0) + (153639231716619/25000000000000 : ℝ)*(major1) + (1229113460529/200000000000 : ℝ)*(major2) + (767853999/100000000000000 : ℝ)*(sp2) + (162944905810169/20000000000000 : ℝ)*(sp4) + (50920194566041/6250000000000 : ℝ)*(sp5) + (407361150300081/50000000000000 : ℝ)*(sp6) + (414388892047429/100000000000000 : ℝ)*(sp7) + (414388892047429/100000000000000 : ℝ)*(f.failure) + (814724725652821/100000000000000 : ℝ)*(f.sum) + (33251323387/195312500000000000000000000 : ℝ)*base66 + (18962468861/12500000000000000000000000 : ℝ)*base68 + (35362927725433/3125000000000000000000000000 : ℝ)*base69 + (55288135397/25000000000000000000000000 : ℝ)*base72 + (196184774899/390625000000000000000000000 : ℝ)*base74 + (10733058304471/1562500000000000000000000000 : ℝ)*base76 + (620073973101/390625000000000000000000000 : ℝ)*base77 + (5158987837933/3125000000000000000000000000 : ℝ)*base79 + (2319586164759/3125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (873979/1250000000000000000000 : ℝ)*base90 + (873979/1250000000000000000000 : ℝ)*base92 + (873979/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1082_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (41/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28047/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1082_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1082_s1_0 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119930363/10000000000 : ℝ)*x 0 + (228714387/400000000 : ℝ)*x 1 + (4989456679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119930363/10000000000 : ℝ)^8275 ≤ (6363928561007/50000000000000 : ℝ)^6227 := by
    have hnat : (2119930363 : ℕ)^8275*50000000000000^6227 ≤ 6363928561007^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119930363 10000000000 6363928561007 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228714387/400000000 : ℝ)^8275 ≤ (23788110319851/50000000000000 : ℝ)^6227 := by
    have hnat : (228714387 : ℕ)^8275*50000000000000^6227 ≤ 23788110319851^6227*400000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228714387 400000000 23788110319851 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4989456679/10000000000 : ℝ)^8275 ≤ (39695922233617/100000000000000 : ℝ)^6227 := by
    have hnat : (4989456679 : ℕ)^8275*100000000000000^6227 ≤ 39695922233617^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989456679 10000000000 39695922233617 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119930363/10000000000 : ℝ), (228714387/400000000 : ℝ), (4989456679/10000000000 : ℝ)] ![(6363928561007/50000000000000 : ℝ), (23788110319851/50000000000000 : ℝ), (39695922233617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119930363/10000000000 : ℝ)|^8275 ≤ (6363928561007/50000000000000 : ℝ)^6227
        have hw : |(-2119930363/10000000000 : ℝ)|=(2119930363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228714387/400000000 : ℝ)|^8275 ≤ (23788110319851/50000000000000 : ℝ)^6227
        have hw : |(228714387/400000000 : ℝ)|=(228714387/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4989456679/10000000000 : ℝ)|^8275 ≤ (39695922233617/100000000000000 : ℝ)^6227
        have hw : |(4989456679/10000000000 : ℝ)|=(4989456679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s1_1 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2711214761/5000000000 : ℝ)*x 0 + (-314280447/1250000000 : ℝ)*x 1 + (4989456947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711214761/5000000000 : ℝ)^8275 ≤ (22168835115289/50000000000000 : ℝ)^6227 := by
    have hnat : (2711214761 : ℕ)^8275*50000000000000^6227 ≤ 22168835115289^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711214761 5000000000 22168835115289 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314280447/1250000000 : ℝ)^8275 ≤ (3991601169599/25000000000000 : ℝ)^6227 := by
    have hnat : (314280447 : ℕ)^8275*25000000000000^6227 ≤ 3991601169599^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314280447 1250000000 3991601169599 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4989456947/10000000000 : ℝ)^8275 ≤ (19847962533537/50000000000000 : ℝ)^6227 := by
    have hnat : (4989456947 : ℕ)^8275*50000000000000^6227 ≤ 19847962533537^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989456947 10000000000 19847962533537 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711214761/5000000000 : ℝ), (-314280447/1250000000 : ℝ), (4989456947/10000000000 : ℝ)] ![(22168835115289/50000000000000 : ℝ), (3991601169599/25000000000000 : ℝ), (19847962533537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711214761/5000000000 : ℝ)|^8275 ≤ (22168835115289/50000000000000 : ℝ)^6227
        have hw : |(2711214761/5000000000 : ℝ)|=(2711214761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-314280447/1250000000 : ℝ)|^8275 ≤ (3991601169599/25000000000000 : ℝ)^6227
        have hw : |(-314280447/1250000000 : ℝ)|=(314280447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4989456947/10000000000 : ℝ)|^8275 ≤ (19847962533537/50000000000000 : ℝ)^6227
        have hw : |(4989456947/10000000000 : ℝ)|=(4989456947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s1_2 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2711215147/5000000000 : ℝ)*x 0 + (4989456129/10000000000 : ℝ)*x 1 + (-314280451/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711215147/5000000000 : ℝ)^8275 ≤ (44337678619099/100000000000000 : ℝ)^6227 := by
    have hnat : (2711215147 : ℕ)^8275*100000000000000^6227 ≤ 44337678619099^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711215147 5000000000 44337678619099 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4989456129/10000000000 : ℝ)^8275 ≤ (310124347021/781250000000 : ℝ)^6227 := by
    have hnat : (4989456129 : ℕ)^8275*781250000000^6227 ≤ 310124347021^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989456129 10000000000 310124347021 781250000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314280451/1250000000 : ℝ)^8275 ≤ (15966404948443/100000000000000 : ℝ)^6227 := by
    have hnat : (314280451 : ℕ)^8275*100000000000000^6227 ≤ 15966404948443^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314280451 1250000000 15966404948443 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711215147/5000000000 : ℝ), (4989456129/10000000000 : ℝ), (-314280451/1250000000 : ℝ)] ![(44337678619099/100000000000000 : ℝ), (310124347021/781250000000 : ℝ), (15966404948443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711215147/5000000000 : ℝ)|^8275 ≤ (44337678619099/100000000000000 : ℝ)^6227
        have hw : |(2711215147/5000000000 : ℝ)|=(2711215147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4989456129/10000000000 : ℝ)|^8275 ≤ (310124347021/781250000000 : ℝ)^6227
        have hw : |(4989456129/10000000000 : ℝ)|=(4989456129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-314280451/1250000000 : ℝ)|^8275 ≤ (15966404948443/100000000000000 : ℝ)^6227
        have hw : |(-314280451/1250000000 : ℝ)|=(314280451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s1_3 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2161237013/5000000000 : ℝ)*x 0 + (3665624157/10000000000 : ℝ)*x 1 + (5097726981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161237013/5000000000 : ℝ)^8275 ≤ (32804113321997/100000000000000 : ℝ)^6227 := by
    have hnat : (2161237013 : ℕ)^8275*100000000000000^6227 ≤ 32804113321997^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161237013 5000000000 32804113321997 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3665624157/10000000000 : ℝ)^8275 ≤ (26351200776807/100000000000000 : ℝ)^6227 := by
    have hnat : (3665624157 : ℕ)^8275*100000000000000^6227 ≤ 26351200776807^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665624157 10000000000 26351200776807 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5097726981/10000000000 : ℝ)^8275 ≤ (40844685888291/100000000000000 : ℝ)^6227 := by
    have hnat : (5097726981 : ℕ)^8275*100000000000000^6227 ≤ 40844685888291^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097726981 10000000000 40844685888291 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161237013/5000000000 : ℝ), (3665624157/10000000000 : ℝ), (5097726981/10000000000 : ℝ)] ![(32804113321997/100000000000000 : ℝ), (26351200776807/100000000000000 : ℝ), (40844685888291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161237013/5000000000 : ℝ)|^8275 ≤ (32804113321997/100000000000000 : ℝ)^6227
        have hw : |(2161237013/5000000000 : ℝ)|=(2161237013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3665624157/10000000000 : ℝ)|^8275 ≤ (26351200776807/100000000000000 : ℝ)^6227
        have hw : |(3665624157/10000000000 : ℝ)|=(3665624157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5097726981/10000000000 : ℝ)|^8275 ≤ (40844685888291/100000000000000 : ℝ)^6227
        have hw : |(5097726981/10000000000 : ℝ)|=(5097726981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s1_4 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120824291/10000000000 : ℝ)*x 0 + (249981623/500000000 : ℝ)*x 1 + (5707478437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120824291/10000000000 : ℝ)^8275 ≤ (3183747461773/25000000000000 : ℝ)^6227 := by
    have hnat : (2120824291 : ℕ)^8275*25000000000000^6227 ≤ 3183747461773^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120824291 10000000000 3183747461773 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249981623/500000000 : ℝ)^8275 ≤ (39803542754737/100000000000000 : ℝ)^6227 := by
    have hnat : (249981623 : ℕ)^8275*100000000000000^6227 ≤ 39803542754737^6227*500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249981623 500000000 39803542754737 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5707478437/10000000000 : ℝ)^8275 ≤ (47461467389623/100000000000000 : ℝ)^6227 := by
    have hnat : (5707478437 : ℕ)^8275*100000000000000^6227 ≤ 47461467389623^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5707478437 10000000000 47461467389623 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120824291/10000000000 : ℝ), (249981623/500000000 : ℝ), (5707478437/10000000000 : ℝ)] ![(3183747461773/25000000000000 : ℝ), (39803542754737/100000000000000 : ℝ), (47461467389623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120824291/10000000000 : ℝ)|^8275 ≤ (3183747461773/25000000000000 : ℝ)^6227
        have hw : |(-2120824291/10000000000 : ℝ)|=(2120824291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(249981623/500000000 : ℝ)|^8275 ≤ (39803542754737/100000000000000 : ℝ)^6227
        have hw : |(249981623/500000000 : ℝ)|=(249981623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5707478437/10000000000 : ℝ)|^8275 ≤ (47461467389623/100000000000000 : ℝ)^6227
        have hw : |(5707478437/10000000000 : ℝ)|=(5707478437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s1_5 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5236250899/10000000000 : ℝ)*x 0 + (-898110943/5000000000 : ℝ)*x 1 + (5707478291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236250899/10000000000 : ℝ)^8275 ≤ (42326172167563/100000000000000 : ℝ)^6227 := by
    have hnat : (5236250899 : ℕ)^8275*100000000000000^6227 ≤ 42326172167563^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236250899 10000000000 42326172167563 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898110943/5000000000 : ℝ)^8275 ≤ (10212362045671/100000000000000 : ℝ)^6227 := by
    have hnat : (898110943 : ℕ)^8275*100000000000000^6227 ≤ 10212362045671^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898110943 5000000000 10212362045671 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5707478291/10000000000 : ℝ)^8275 ≤ (23730732888117/50000000000000 : ℝ)^6227 := by
    have hnat : (5707478291 : ℕ)^8275*50000000000000^6227 ≤ 23730732888117^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5707478291 10000000000 23730732888117 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236250899/10000000000 : ℝ), (-898110943/5000000000 : ℝ), (5707478291/10000000000 : ℝ)] ![(42326172167563/100000000000000 : ℝ), (10212362045671/100000000000000 : ℝ), (23730732888117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236250899/10000000000 : ℝ)|^8275 ≤ (42326172167563/100000000000000 : ℝ)^6227
        have hw : |(5236250899/10000000000 : ℝ)|=(5236250899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-898110943/5000000000 : ℝ)|^8275 ≤ (10212362045671/100000000000000 : ℝ)^6227
        have hw : |(-898110943/5000000000 : ℝ)|=(898110943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5707478291/10000000000 : ℝ)|^8275 ≤ (23730732888117/50000000000000 : ℝ)^6227
        have hw : |(5707478291/10000000000 : ℝ)|=(5707478291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s1_6 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1309062729/2500000000 : ℝ)*x 0 + (1426869601/2500000000 : ℝ)*x 1 + (-359244339/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309062729/2500000000 : ℝ)^8275 ≤ (21163086175087/50000000000000 : ℝ)^6227 := by
    have hnat : (1309062729 : ℕ)^8275*50000000000000^6227 ≤ 21163086175087^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309062729 2500000000 21163086175087 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426869601/2500000000 : ℝ)^8275 ≤ (47461467024953/100000000000000 : ℝ)^6227 := by
    have hnat : (1426869601 : ℕ)^8275*100000000000000^6227 ≤ 47461467024953^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426869601 2500000000 47461467024953 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359244339/2000000000 : ℝ)^8275 ≤ (10212360602597/100000000000000 : ℝ)^6227 := by
    have hnat : (359244339 : ℕ)^8275*100000000000000^6227 ≤ 10212360602597^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359244339 2000000000 10212360602597 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309062729/2500000000 : ℝ), (1426869601/2500000000 : ℝ), (-359244339/2000000000 : ℝ)] ![(21163086175087/50000000000000 : ℝ), (47461467024953/100000000000000 : ℝ), (10212360602597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309062729/2500000000 : ℝ)|^8275 ≤ (21163086175087/50000000000000 : ℝ)^6227
        have hw : |(1309062729/2500000000 : ℝ)|=(1309062729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426869601/2500000000 : ℝ)|^8275 ≤ (47461467024953/100000000000000 : ℝ)^6227
        have hw : |(1426869601/2500000000 : ℝ)|=(1426869601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-359244339/2000000000 : ℝ)|^8275 ≤ (10212360602597/100000000000000 : ℝ)^6227
        have hw : |(-359244339/2000000000 : ℝ)|=(359244339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s1_7 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4324230927/10000000000 : ℝ)*x 0 + (5077721287/10000000000 : ℝ)*x 1 + (460754237/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324230927/10000000000 : ℝ)^8275 ≤ (4102729153239/12500000000000 : ℝ)^6227 := by
    have hnat : (4324230927 : ℕ)^8275*12500000000000^6227 ≤ 4102729153239^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324230927 10000000000 4102729153239 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5077721287/10000000000 : ℝ)^8275 ≤ (40631812616173/100000000000000 : ℝ)^6227 := by
    have hnat : (5077721287 : ℕ)^8275*100000000000000^6227 ≤ 40631812616173^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077721287 10000000000 40631812616173 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460754237/1250000000 : ℝ)^8275 ≤ (3318294267079/12500000000000 : ℝ)^6227 := by
    have hnat : (460754237 : ℕ)^8275*12500000000000^6227 ≤ 3318294267079^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460754237 1250000000 3318294267079 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324230927/10000000000 : ℝ), (5077721287/10000000000 : ℝ), (460754237/1250000000 : ℝ)] ![(4102729153239/12500000000000 : ℝ), (40631812616173/100000000000000 : ℝ), (3318294267079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324230927/10000000000 : ℝ)|^8275 ≤ (4102729153239/12500000000000 : ℝ)^6227
        have hw : |(4324230927/10000000000 : ℝ)|=(4324230927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5077721287/10000000000 : ℝ)|^8275 ≤ (40631812616173/100000000000000 : ℝ)^6227
        have hw : |(5077721287/10000000000 : ℝ)|=(5077721287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(460754237/1250000000 : ℝ)|^8275 ≤ (3318294267079/12500000000000 : ℝ)^6227
        have hw : |(460754237/1250000000 : ℝ)|=(460754237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1082_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (41/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5307/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4143/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (41/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (41/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (41/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (41/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (41/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (41/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (41/25000 : ℝ) ^ (4137/1024 : ℝ) ≤ (559577639/100000000000000000000 : ℝ) := by
    have hpowers : (41/25000 : ℝ)^4137 ≤ (559577639/100000000000000000000 : ℝ)^1024 := by
      have hnat : (41 : ℕ)^4137*100000000000000000000^1024 ≤ 559577639^1024*25000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41 25000 559577639 100000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41/25000 : ℝ)) (X := (559577639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (28047/100000 : ℝ) ^ (4137/1024 : ℝ) ≤ (588084249063462527/100000000000000000000 : ℝ) := by
    have hpowers : (28047/100000 : ℝ)^4137 ≤ (588084249063462527/100000000000000000000 : ℝ)^1024 := by
      have hnat : (28047 : ℕ)^4137*100000000000000000000^1024 ≤ 588084249063462527^1024*100000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28047 100000 588084249063462527 100000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28047/100000 : ℝ)) (X := (588084249063462527/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000559577639/50000000000000000000 : ℝ) ≤ (5000000000013851/5000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (50000000000559577639/50000000000000000000 : ℝ)^1024 ≤ (5000000000013851/5000000000000000 : ℝ)^4137 := by
      have hnat : (50000000000559577639 : ℕ)^1024*5000000000000000^4137 ≤ 5000000000013851^4137*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000559577639 50000000000000000000 5000000000013851 5000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000013851/5000000000000000 : ℝ)) (X := (50000000000559577639/50000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50294042124811520083/50000000000000000000 : ℝ) ≤ (5007262151388327/5000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (50294042124811520083/50000000000000000000 : ℝ)^1024 ≤ (5007262151388327/5000000000000000 : ℝ)^4137 := by
      have hnat : (50294042124811520083 : ℕ)^1024*5000000000000000^4137 ≤ 5007262151388327^4137*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50294042124811520083 50000000000000000000 5007262151388327 5000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007262151388327/5000000000000000 : ℝ)) (X := (50294042124811520083/50000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50588084249063462527/50000000000000000000 : ℝ) ≤ (5014524302762803/5000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (50588084249063462527/50000000000000000000 : ℝ)^1024 ≤ (5014524302762803/5000000000000000 : ℝ)^4137 := by
      have hnat : (50588084249063462527 : ℕ)^1024*5000000000000000^4137 ≤ 5014524302762803^4137*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50588084249063462527 50000000000000000000 5014524302762803 5000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014524302762803/5000000000000000 : ℝ)) (X := (50588084249063462527/50000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(559577639/100000000000000000000 : ℝ) ≤ ((27882523602947075861/27883000000000000000 : ℝ)+2*(1815537843619/348537500000000 : ℝ)*(41/25000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (27882523602947075861/27883000000000000000 : ℝ)+2*(1815537843619/348537500000000 : ℝ)*(41/25000 : ℝ)=(5000000000013851/5000000000000000 : ℝ) by norm_num, show 1+2*(559577639/100000000000000000000 : ℝ)=(50000000000559577639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(588084249063462527/100000000000000000000 : ℝ)+(559577639/100000000000000000000 : ℝ) ≤ ((27882523602947075861/27883000000000000000 : ℝ)+(1815537843619/348537500000000 : ℝ)*((28047/100000 : ℝ)+(41/25000 : ℝ)))^(4137/1024 : ℝ) := by
    rw [show (27882523602947075861/27883000000000000000 : ℝ)+(1815537843619/348537500000000 : ℝ)*((28047/100000 : ℝ)+(41/25000 : ℝ))=(5007262151388327/5000000000000000 : ℝ) by norm_num, show 1+(588084249063462527/100000000000000000000 : ℝ)+(559577639/100000000000000000000 : ℝ)=(50294042124811520083/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(588084249063462527/100000000000000000000 : ℝ) ≤ ((27882523602947075861/27883000000000000000 : ℝ)+2*(1815537843619/348537500000000 : ℝ)*(28047/100000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (27882523602947075861/27883000000000000000 : ℝ)+2*(1815537843619/348537500000000 : ℝ)*(28047/100000 : ℝ)=(5014524302762803/5000000000000000 : ℝ) by norm_num, show 1+2*(588084249063462527/100000000000000000000 : ℝ)=(50588084249063462527/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27882523602947075861/27883000000000000000 : ℝ)*(X 1 0+X 2 0)+(1815537843619/348537500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (41/25000 : ℝ)) (hi := (28047/100000 : ℝ)) (c := (27882523602947075861/27883000000000000000 : ℝ)) (alpha := (1815537843619/348537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27882523602947075861/27883000000000000000 : ℝ)*(X 0 1+X 2 1)+(1815537843619/348537500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (41/25000 : ℝ)) (hi := (28047/100000 : ℝ)) (c := (27882523602947075861/27883000000000000000 : ℝ)) (alpha := (1815537843619/348537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27882523602947075861/27883000000000000000 : ℝ)*(X 0 2+X 1 2)+(1815537843619/348537500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (41/25000 : ℝ)) (hi := (28047/100000 : ℝ)) (c := (27882523602947075861/27883000000000000000 : ℝ)) (alpha := (1815537843619/348537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2119930363/10000000000 : ℝ)*X 0 0+(228714387/400000000 : ℝ)*X 0 1+(4989456679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2711214761/5000000000 : ℝ)*X 1 0+(-314280447/1250000000 : ℝ)*X 1 1+(4989456947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2711215147/5000000000 : ℝ)*X 2 0+(4989456129/10000000000 : ℝ)*X 2 1+(-314280451/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161237013/5000000000 : ℝ)*X 0 0+(3665624157/10000000000 : ℝ)*X 0 1+(5097726981/10000000000 : ℝ)*X 0 2+(2161237013/5000000000 : ℝ)*X 1 0+(3665624157/10000000000 : ℝ)*X 1 1+(5097726981/10000000000 : ℝ)*X 1 2+(2161237013/5000000000 : ℝ)*X 2 0+(3665624157/10000000000 : ℝ)*X 2 1+(5097726981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2120824291/10000000000 : ℝ)*X 0 0+(249981623/500000000 : ℝ)*X 0 1+(5707478437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5236250899/10000000000 : ℝ)*X 1 0+(-898110943/5000000000 : ℝ)*X 1 1+(5707478291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1309062729/2500000000 : ℝ)*X 2 0+(1426869601/2500000000 : ℝ)*X 2 1+(-359244339/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324230927/10000000000 : ℝ)*X 0 0+(5077721287/10000000000 : ℝ)*X 0 1+(460754237/1250000000 : ℝ)*X 0 2+(4324230927/10000000000 : ℝ)*X 1 0+(5077721287/10000000000 : ℝ)*X 1 1+(460754237/1250000000 : ℝ)*X 1 2+(4324230927/10000000000 : ℝ)*X 2 0+(5077721287/10000000000 : ℝ)*X 2 1+(460754237/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (663663729048503775134491779/174268750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7281009/6250000000000 : ℝ)*(base1) + (75729947/10000000000000 : ℝ)*(base19) + (952757571/100000000000000 : ℝ)*(base23) + (59216929/100000000000000 : ℝ)*(upper3) + (25361077/25000000000000 : ℝ)*(upper5) + (258893850601663/25000000000000 : ℝ)*(major0) + (258893850601663/25000000000000 : ℝ)*(major1) + (258893850601663/25000000000000 : ℝ)*(major2) + (21451088592723/1562500000000 : ℝ)*(sp0) + (686436479475613/50000000000000 : ℝ)*(sp1) + (2196596421589/160000000000 : ℝ)*(sp2) + (698275334013297/100000000000000 : ℝ)*(sp3) + (520351571/12500000000000 : ℝ)*(sp4) + (188888823/12500000000000 : ℝ)*(sp7) + (349138480810013/50000000000000 : ℝ)*(f.failure) + (171609214531337/12500000000000 : ℝ)*(f.sum) + (178872720076157/69707500000000000000000000000 : ℝ)*base65 + (4973659331832258157/697075000000000000000000000000000 : ℝ)*base68 + (974166709038858157/697075000000000000000000000000000 : ℝ)*base70 + (2596280126468133157/697075000000000000000000000000000 : ℝ)*base72 + (396911857770611/139415000000000000000000000000 : ℝ)*base74 + (2609412727393708157/697075000000000000000000000000000 : ℝ)*base76 + (24558215657516843/697075000000000000000000000000000 : ℝ)*base77 + (2424159273665633157/697075000000000000000000000000000 : ℝ)*base80 + (145073217461989/139415000000000000000000000000 : ℝ)*base81 + (5684637/625000000000000000000 : ℝ)*base89 + (5684637/625000000000000000000 : ℝ)*base91 + (5684637/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2088923862182074780035898119/348537500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35711653/50000000000000 : ℝ)*(base1) + (1346348059/100000000000000 : ℝ)*(base19) + (170550231/12500000000000 : ℝ)*(base23) + (136038201/100000000000000 : ℝ)*(upper3) + (8463319/6250000000000 : ℝ)*(upper5) + (266411144347869/25000000000000 : ℝ)*(major0) + (266411144347869/25000000000000 : ℝ)*(major1) + (266411144347869/25000000000000 : ℝ)*(major2) + (5299201417/100000000000000 : ℝ)*(sp1) + (1419485477/25000000000000 : ℝ)*(sp2) + (88296047185373/6250000000000 : ℝ)*(sp4) + (282546007598637/20000000000000 : ℝ)*(sp5) + (282545928239781/20000000000000 : ℝ)*(sp6) + (718552200037053/100000000000000 : ℝ)*(sp7) + (17963806786509/2500000000000 : ℝ)*(f.failure) + (1412736683542661/100000000000000 : ℝ)*(f.sum) + (371522679237307/139415000000000000000000000000 : ℝ)*base65 + (1401305614785745209/697075000000000000000000000000000 : ℝ)*base67 + (2527979563323770209/697075000000000000000000000000000 : ℝ)*base69 + (3398128794450570209/697075000000000000000000000000000 : ℝ)*base71 + (392038479541917/139415000000000000000000000000 : ℝ)*base73 + (4502438423723920209/697075000000000000000000000000000 : ℝ)*base75 + (2367397491283845209/697075000000000000000000000000000 : ℝ)*base77 + (6891203097266345209/697075000000000000000000000000000 : ℝ)*base79 + (825657142435817/139415000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (130941/31250000000000000000 : ℝ)*base89 + (130941/31250000000000000000 : ℝ)*base91 + (130941/31250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1082_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (41/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4143/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1082_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1082_s2_0 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2176453683/10000000000 : ℝ)*x 0 + (2761309883/5000000000 : ℝ)*x 1 + (2574409183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176453683/10000000000 : ℝ)^8275 ≤ (13180795733937/100000000000000 : ℝ)^6227 := by
    have hnat : (2176453683 : ℕ)^8275*100000000000000^6227 ≤ 13180795733937^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176453683 10000000000 13180795733937 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2761309883/5000000000 : ℝ)^8275 ≤ (45429627667859/100000000000000 : ℝ)^6227 := by
    have hnat : (2761309883 : ℕ)^8275*100000000000000^6227 ≤ 45429627667859^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761309883 5000000000 45429627667859 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2574409183/5000000000 : ℝ)^8275 ≤ (20694788291333/50000000000000 : ℝ)^6227 := by
    have hnat : (2574409183 : ℕ)^8275*50000000000000^6227 ≤ 20694788291333^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574409183 5000000000 20694788291333 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2176453683/10000000000 : ℝ), (2761309883/5000000000 : ℝ), (2574409183/5000000000 : ℝ)] ![(13180795733937/100000000000000 : ℝ), (45429627667859/100000000000000 : ℝ), (20694788291333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2176453683/10000000000 : ℝ)|^8275 ≤ (13180795733937/100000000000000 : ℝ)^6227
        have hw : |(-2176453683/10000000000 : ℝ)|=(2176453683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2761309883/5000000000 : ℝ)|^8275 ≤ (45429627667859/100000000000000 : ℝ)^6227
        have hw : |(2761309883/5000000000 : ℝ)|=(2761309883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2574409183/5000000000 : ℝ)|^8275 ≤ (20694788291333/50000000000000 : ℝ)^6227
        have hw : |(2574409183/5000000000 : ℝ)|=(2574409183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s2_1 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2688244197/5000000000 : ℝ)*x 0 + (-1185632529/5000000000 : ℝ)*x 1 + (2574409441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688244197/5000000000 : ℝ)^8275 ≤ (43839172610701/100000000000000 : ℝ)^6227 := by
    have hnat : (2688244197 : ℕ)^8275*100000000000000^6227 ≤ 43839172610701^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688244197 5000000000 43839172610701 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1185632529/5000000000 : ℝ)^8275 ≤ (14771245277709/100000000000000 : ℝ)^6227 := by
    have hnat : (1185632529 : ℕ)^8275*100000000000000^6227 ≤ 14771245277709^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185632529 5000000000 14771245277709 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2574409441/5000000000 : ℝ)^8275 ≤ (2586848880927/6250000000000 : ℝ)^6227 := by
    have hnat : (2574409441 : ℕ)^8275*6250000000000^6227 ≤ 2586848880927^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574409441 5000000000 2586848880927 6250000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688244197/5000000000 : ℝ), (-1185632529/5000000000 : ℝ), (2574409441/5000000000 : ℝ)] ![(43839172610701/100000000000000 : ℝ), (14771245277709/100000000000000 : ℝ), (2586848880927/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688244197/5000000000 : ℝ)|^8275 ≤ (43839172610701/100000000000000 : ℝ)^6227
        have hw : |(2688244197/5000000000 : ℝ)|=(2688244197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1185632529/5000000000 : ℝ)|^8275 ≤ (14771245277709/100000000000000 : ℝ)^6227
        have hw : |(-1185632529/5000000000 : ℝ)|=(1185632529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2574409441/5000000000 : ℝ)|^8275 ≤ (2586848880927/6250000000000 : ℝ)^6227
        have hw : |(2574409441/5000000000 : ℝ)|=(2574409441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s2_2 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1344122137/2500000000 : ℝ)*x 0 + (643602339/1250000000 : ℝ)*x 1 + (-94850603/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344122137/2500000000 : ℝ)^8275 ≤ (43839174279383/100000000000000 : ℝ)^6227 := by
    have hnat : (1344122137 : ℕ)^8275*100000000000000^6227 ≤ 43839174279383^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344122137 2500000000 43839174279383 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643602339/1250000000 : ℝ)^8275 ≤ (5173697534851/12500000000000 : ℝ)^6227 := by
    have hnat : (643602339 : ℕ)^8275*12500000000000^6227 ≤ 5173697534851^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643602339 1250000000 5173697534851 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94850603/400000000 : ℝ)^8275 ≤ (3692811354609/25000000000000 : ℝ)^6227 := by
    have hnat : (94850603 : ℕ)^8275*25000000000000^6227 ≤ 3692811354609^6227*400000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94850603 400000000 3692811354609 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344122137/2500000000 : ℝ), (643602339/1250000000 : ℝ), (-94850603/400000000 : ℝ)] ![(43839174279383/100000000000000 : ℝ), (5173697534851/12500000000000 : ℝ), (3692811354609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344122137/2500000000 : ℝ)|^8275 ≤ (43839174279383/100000000000000 : ℝ)^6227
        have hw : |(1344122137/2500000000 : ℝ)|=(1344122137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643602339/1250000000 : ℝ)|^8275 ≤ (5173697534851/12500000000000 : ℝ)^6227
        have hw : |(643602339/1250000000 : ℝ)|=(643602339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94850603/400000000 : ℝ)|^8275 ≤ (3692811354609/25000000000000 : ℝ)^6227
        have hw : |(-94850603/400000000 : ℝ)|=(94850603/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s2_3 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090271973/2500000000 : ℝ)*x 0 + (4009179401/10000000000 : ℝ)*x 1 + (4744104741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090271973/2500000000 : ℝ)^8275 ≤ (33194113306833/100000000000000 : ℝ)^6227 := by
    have hnat : (1090271973 : ℕ)^8275*100000000000000^6227 ≤ 33194113306833^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090271973 2500000000 33194113306833 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4009179401/10000000000 : ℝ)^8275 ≤ (5936552059147/20000000000000 : ℝ)^6227 := by
    have hnat : (4009179401 : ℕ)^8275*20000000000000^6227 ≤ 5936552059147^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009179401 10000000000 5936552059147 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4744104741/10000000000 : ℝ)^8275 ≤ (37123126385303/100000000000000 : ℝ)^6227 := by
    have hnat : (4744104741 : ℕ)^8275*100000000000000^6227 ≤ 37123126385303^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4744104741 10000000000 37123126385303 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090271973/2500000000 : ℝ), (4009179401/10000000000 : ℝ), (4744104741/10000000000 : ℝ)] ![(33194113306833/100000000000000 : ℝ), (5936552059147/20000000000000 : ℝ), (37123126385303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090271973/2500000000 : ℝ)|^8275 ≤ (33194113306833/100000000000000 : ℝ)^6227
        have hw : |(1090271973/2500000000 : ℝ)|=(1090271973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4009179401/10000000000 : ℝ)|^8275 ≤ (5936552059147/20000000000000 : ℝ)^6227
        have hw : |(4009179401/10000000000 : ℝ)|=(4009179401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4744104741/10000000000 : ℝ)|^8275 ≤ (37123126385303/100000000000000 : ℝ)^6227
        have hw : |(4744104741/10000000000 : ℝ)|=(4744104741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s2_4 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-68017947/312500000 : ℝ)*x 0 + (1287876729/2500000000 : ℝ)*x 1 + (5519903231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68017947/312500000 : ℝ)^8275 ≤ (13181766485771/100000000000000 : ℝ)^6227 := by
    have hnat : (68017947 : ℕ)^8275*100000000000000^6227 ≤ 13181766485771^6227*312500000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68017947 312500000 13181766485771 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1287876729/2500000000 : ℝ)^8275 ≤ (41418299460591/100000000000000 : ℝ)^6227 := by
    have hnat : (1287876729 : ℕ)^8275*100000000000000^6227 ≤ 41418299460591^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287876729 2500000000 41418299460591 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5519903231/10000000000 : ℝ)^8275 ≤ (45399934034553/100000000000000 : ℝ)^6227 := by
    have hnat : (5519903231 : ℕ)^8275*100000000000000^6227 ≤ 45399934034553^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519903231 10000000000 45399934034553 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68017947/312500000 : ℝ), (1287876729/2500000000 : ℝ), (5519903231/10000000000 : ℝ)] ![(13181766485771/100000000000000 : ℝ), (41418299460591/100000000000000 : ℝ), (45399934034553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68017947/312500000 : ℝ)|^8275 ≤ (13181766485771/100000000000000 : ℝ)^6227
        have hw : |(-68017947/312500000 : ℝ)|=(68017947/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1287876729/2500000000 : ℝ)|^8275 ≤ (41418299460591/100000000000000 : ℝ)^6227
        have hw : |(1287876729/2500000000 : ℝ)|=(1287876729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5519903231/10000000000 : ℝ)|^8275 ≤ (45399934034553/100000000000000 : ℝ)^6227
        have hw : |(5519903231/10000000000 : ℝ)|=(5519903231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s2_5 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056406301/2000000000 : ℝ)*x 0 + (-100009031/500000000 : ℝ)*x 1 + (5519903327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056406301/2000000000 : ℝ)^8275 ≤ (21409322321069/50000000000000 : ℝ)^6227 := by
    have hnat : (1056406301 : ℕ)^8275*50000000000000^6227 ≤ 21409322321069^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056406301 2000000000 21409322321069 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100009031/500000000 : ℝ)^8275 ≤ (11781420256579/100000000000000 : ℝ)^6227 := by
    have hnat : (100009031 : ℕ)^8275*100000000000000^6227 ≤ 11781420256579^6227*500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100009031 500000000 11781420256579 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5519903327/10000000000 : ℝ)^8275 ≤ (9079987016763/20000000000000 : ℝ)^6227 := by
    have hnat : (5519903327 : ℕ)^8275*20000000000000^6227 ≤ 9079987016763^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519903327 10000000000 9079987016763 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056406301/2000000000 : ℝ), (-100009031/500000000 : ℝ), (5519903327/10000000000 : ℝ)] ![(21409322321069/50000000000000 : ℝ), (11781420256579/100000000000000 : ℝ), (9079987016763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056406301/2000000000 : ℝ)|^8275 ≤ (21409322321069/50000000000000 : ℝ)^6227
        have hw : |(1056406301/2000000000 : ℝ)|=(1056406301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100009031/500000000 : ℝ)|^8275 ≤ (11781420256579/100000000000000 : ℝ)^6227
        have hw : |(-100009031/500000000 : ℝ)|=(100009031/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5519903327/10000000000 : ℝ)|^8275 ≤ (9079987016763/20000000000000 : ℝ)^6227
        have hw : |(5519903327/10000000000 : ℝ)|=(5519903327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s2_6 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (264101587/500000000 : ℝ)*x 0 + (2759951587/5000000000 : ℝ)*x 1 + (-200018051/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264101587/500000000 : ℝ)^8275 ≤ (21409323586851/50000000000000 : ℝ)^6227 := by
    have hnat : (264101587 : ℕ)^8275*50000000000000^6227 ≤ 21409323586851^6227*500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264101587 500000000 21409323586851 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2759951587/5000000000 : ℝ)^8275 ≤ (45399933411553/100000000000000 : ℝ)^6227 := by
    have hnat : (2759951587 : ℕ)^8275*100000000000000^6227 ≤ 45399933411553^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759951587 5000000000 45399933411553 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200018051/1000000000 : ℝ)^8275 ≤ (2356283879113/20000000000000 : ℝ)^6227 := by
    have hnat : (200018051 : ℕ)^8275*20000000000000^6227 ≤ 2356283879113^6227*1000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200018051 1000000000 2356283879113 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264101587/500000000 : ℝ), (2759951587/5000000000 : ℝ), (-200018051/1000000000 : ℝ)] ![(21409323586851/50000000000000 : ℝ), (45399933411553/100000000000000 : ℝ), (2356283879113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264101587/500000000 : ℝ)|^8275 ≤ (21409323586851/50000000000000 : ℝ)^6227
        have hw : |(264101587/500000000 : ℝ)|=(264101587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2759951587/5000000000 : ℝ)|^8275 ≤ (45399933411553/100000000000000 : ℝ)^6227
        have hw : |(2759951587/5000000000 : ℝ)|=(2759951587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200018051/1000000000 : ℝ)|^8275 ≤ (2356283879113/20000000000000 : ℝ)^6227
        have hw : |(-200018051/1000000000 : ℝ)|=(200018051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s2_7 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361325203/10000000000 : ℝ)*x 0 + (4738819369/10000000000 : ℝ)*x 1 + (4014519443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361325203/10000000000 : ℝ)^8275 ≤ (6639302734189/20000000000000 : ℝ)^6227 := by
    have hnat : (4361325203 : ℕ)^8275*20000000000000^6227 ≤ 6639302734189^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361325203 10000000000 6639302734189 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4738819369/10000000000 : ℝ)^8275 ≤ (37068175413357/100000000000000 : ℝ)^6227 := by
    have hnat : (4738819369 : ℕ)^8275*100000000000000^6227 ≤ 37068175413357^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4738819369 10000000000 37068175413357 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4014519443/10000000000 : ℝ)^8275 ≤ (14867655448559/50000000000000 : ℝ)^6227 := by
    have hnat : (4014519443 : ℕ)^8275*50000000000000^6227 ≤ 14867655448559^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014519443 10000000000 14867655448559 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361325203/10000000000 : ℝ), (4738819369/10000000000 : ℝ), (4014519443/10000000000 : ℝ)] ![(6639302734189/20000000000000 : ℝ), (37068175413357/100000000000000 : ℝ), (14867655448559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361325203/10000000000 : ℝ)|^8275 ≤ (6639302734189/20000000000000 : ℝ)^6227
        have hw : |(4361325203/10000000000 : ℝ)|=(4361325203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4738819369/10000000000 : ℝ)|^8275 ≤ (37068175413357/100000000000000 : ℝ)^6227
        have hw : |(4738819369/10000000000 : ℝ)|=(4738819369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4014519443/10000000000 : ℝ)|^8275 ≤ (14867655448559/50000000000000 : ℝ)^6227
        have hw : |(4014519443/10000000000 : ℝ)|=(4014519443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1082_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4143/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (879/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16689/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4143/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4143/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4143/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4143/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4143/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4143/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5307/100000 : ℝ) ^ (4137/1024 : ℝ) ≤ (176311447965927/25000000000000000000 : ℝ) := by
    have hpowers : (5307/100000 : ℝ)^4137 ≤ (176311447965927/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5307 : ℕ)^4137*25000000000000000000^1024 ≤ 176311447965927^1024*100000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5307 100000 176311447965927 25000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5307/100000 : ℝ)) (X := (176311447965927/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4143/20000 : ℝ) ^ (4137/1024 : ℝ) ≤ (10805489801227521/6250000000000000000 : ℝ) := by
    have hpowers : (4143/20000 : ℝ)^4137 ≤ (10805489801227521/6250000000000000000 : ℝ)^1024 := by
      have hnat : (4143 : ℕ)^4137*6250000000000000000^1024 ≤ 10805489801227521^1024*20000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4143 20000 10805489801227521 6250000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4143/20000 : ℝ)) (X := (10805489801227521/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500176311447965927/12500000000000000000 : ℝ) ≤ (10000034912635169/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (12500176311447965927/12500000000000000000 : ℝ)^1024 ≤ (10000034912635169/10000000000000000 : ℝ)^4137 := by
      have hnat : (12500176311447965927 : ℕ)^1024*10000000000000000^4137 ≤ 10000034912635169^4137*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500176311447965927 12500000000000000000 10000034912635169 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000034912635169/10000000000000000 : ℝ)) (X := (12500176311447965927/12500000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25043398270652876011/25000000000000000000 : ℝ) ≤ (10004294013420559/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (25043398270652876011/25000000000000000000 : ℝ)^1024 ≤ (10004294013420559/10000000000000000 : ℝ)^4137 := by
      have hnat : (25043398270652876011 : ℕ)^1024*10000000000000000^4137 ≤ 10004294013420559^4137*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25043398270652876011 25000000000000000000 10004294013420559 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004294013420559/10000000000000000 : ℝ)) (X := (25043398270652876011/25000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3135805489801227521/3125000000000000000 : ℝ) ≤ (10008553114205949/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (3135805489801227521/3125000000000000000 : ℝ)^1024 ≤ (10008553114205949/10000000000000000 : ℝ)^4137 := by
      have hnat : (3135805489801227521 : ℕ)^1024*10000000000000000^4137 ≤ 10008553114205949^4137*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3135805489801227521 3125000000000000000 10008553114205949 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008553114205949/10000000000000000 : ℝ)) (X := (3135805489801227521/3125000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(176311447965927/25000000000000000000 : ℝ) ≤ ((12836277653178879541/12840000000000000000 : ℝ)+2*(425910078539/154080000000000 : ℝ)*(5307/100000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (12836277653178879541/12840000000000000000 : ℝ)+2*(425910078539/154080000000000 : ℝ)*(5307/100000 : ℝ)=(10000034912635169/10000000000000000 : ℝ) by norm_num, show 1+2*(176311447965927/25000000000000000000 : ℝ)=(12500176311447965927/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10805489801227521/6250000000000000000 : ℝ)+(176311447965927/25000000000000000000 : ℝ) ≤ ((12836277653178879541/12840000000000000000 : ℝ)+(425910078539/154080000000000 : ℝ)*((4143/20000 : ℝ)+(5307/100000 : ℝ)))^(4137/1024 : ℝ) := by
    rw [show (12836277653178879541/12840000000000000000 : ℝ)+(425910078539/154080000000000 : ℝ)*((4143/20000 : ℝ)+(5307/100000 : ℝ))=(10004294013420559/10000000000000000 : ℝ) by norm_num, show 1+(10805489801227521/6250000000000000000 : ℝ)+(176311447965927/25000000000000000000 : ℝ)=(25043398270652876011/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10805489801227521/6250000000000000000 : ℝ) ≤ ((12836277653178879541/12840000000000000000 : ℝ)+2*(425910078539/154080000000000 : ℝ)*(4143/20000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (12836277653178879541/12840000000000000000 : ℝ)+2*(425910078539/154080000000000 : ℝ)*(4143/20000 : ℝ)=(10008553114205949/10000000000000000 : ℝ) by norm_num, show 1+2*(10805489801227521/6250000000000000000 : ℝ)=(3135805489801227521/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12836277653178879541/12840000000000000000 : ℝ)*(X 1 0+X 2 0)+(425910078539/154080000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (5307/100000 : ℝ)) (hi := (4143/20000 : ℝ)) (c := (12836277653178879541/12840000000000000000 : ℝ)) (alpha := (425910078539/154080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12836277653178879541/12840000000000000000 : ℝ)*(X 0 1+X 2 1)+(425910078539/154080000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (5307/100000 : ℝ)) (hi := (4143/20000 : ℝ)) (c := (12836277653178879541/12840000000000000000 : ℝ)) (alpha := (425910078539/154080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12836277653178879541/12840000000000000000 : ℝ)*(X 0 2+X 1 2)+(425910078539/154080000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (5307/100000 : ℝ)) (hi := (4143/20000 : ℝ)) (c := (12836277653178879541/12840000000000000000 : ℝ)) (alpha := (425910078539/154080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2176453683/10000000000 : ℝ)*X 0 0+(2761309883/5000000000 : ℝ)*X 0 1+(2574409183/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2688244197/5000000000 : ℝ)*X 1 0+(-1185632529/5000000000 : ℝ)*X 1 1+(2574409441/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1344122137/2500000000 : ℝ)*X 2 0+(643602339/1250000000 : ℝ)*X 2 1+(-94850603/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090271973/2500000000 : ℝ)*X 0 0+(4009179401/10000000000 : ℝ)*X 0 1+(4744104741/10000000000 : ℝ)*X 0 2+(1090271973/2500000000 : ℝ)*X 1 0+(4009179401/10000000000 : ℝ)*X 1 1+(4744104741/10000000000 : ℝ)*X 1 2+(1090271973/2500000000 : ℝ)*X 2 0+(4009179401/10000000000 : ℝ)*X 2 1+(4744104741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-68017947/312500000 : ℝ)*X 0 0+(1287876729/2500000000 : ℝ)*X 0 1+(5519903231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1056406301/2000000000 : ℝ)*X 1 0+(-100009031/500000000 : ℝ)*X 1 1+(5519903327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264101587/500000000 : ℝ)*X 2 0+(2759951587/5000000000 : ℝ)*X 2 1+(-200018051/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361325203/10000000000 : ℝ)*X 0 0+(4738819369/10000000000 : ℝ)*X 0 1+(4014519443/10000000000 : ℝ)*X 0 2+(4361325203/10000000000 : ℝ)*X 1 0+(4738819369/10000000000 : ℝ)*X 1 1+(4014519443/10000000000 : ℝ)*X 1 2+(4361325203/10000000000 : ℝ)*X 2 0+(4738819369/10000000000 : ℝ)*X 2 1+(4014519443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (716080200173385471402808563/214000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20582449/4000000000000 : ℝ)*(base19) + (143827689/25000000000000 : ℝ)*(base23) + (58697513/100000000000000 : ℝ)*(upper3) + (853669/10000000000000 : ℝ)*(upper4) + (13292503/25000000000000 : ℝ)*(upper5) + (2017962084686343/100000000000000 : ℝ)*(major0) + (2017962084686343/100000000000000 : ℝ)*(major1) + (2017962084686343/100000000000000 : ℝ)*(major2) + (133761291562019/5000000000000 : ℝ)*(sp0) + (21401873453613/800000000000 : ℝ)*(sp1) + (1337617060476047/50000000000000 : ℝ)*(sp2) + (272137153366077/20000000000000 : ℝ)*(sp3) + (886502247/10000000000000 : ℝ)*(sp4) + (3594740473/100000000000000 : ℝ)*(sp7) + (680344680785429/50000000000000 : ℝ)*(f.failure) + (53504693925257/2000000000000 : ℝ)*(f.sum) + (12535528670167/2568000000000000000000000000 : ℝ)*base65 + (13572520853343441437/1284000000000000000000000000000000 : ℝ)*base68 + (1222388619711441437/1284000000000000000000000000000000 : ℝ)*base70 + (3923384912228558563/1284000000000000000000000000000000 : ℝ)*base71 + (2751499662737/2568000000000000000000000000 : ℝ)*base74 + (8341736682111441437/1284000000000000000000000000000000 : ℝ)*base76 + (4119821260179441437/1284000000000000000000000000000000 : ℝ)*base78 + (5357453489504558563/1284000000000000000000000000000000 : ℝ)*base79 + (15405921571327/2568000000000000000000000000 : ℝ)*base81 + (2461979/625000000000000000000 : ℝ)*base90 + (2461979/625000000000000000000 : ℝ)*base92 + (2461979/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3045835068579815697909309/342400000000000000000000000000 : ℝ) := by norm_num
    linear_combination (875960953/50000000000000 : ℝ)*(base19) + (1011304891/50000000000000 : ℝ)*(base23) + (234623703/100000000000000 : ℝ)*(upper3) + (53291347/100000000000000 : ℝ)*(lower4) + (36187181/20000000000000 : ℝ)*(upper5) + (3276089144649/160000000000 : ℝ)*(major0) + (3276089144649/160000000000 : ℝ)*(major1) + (3276089144649/160000000000 : ℝ)*(major2) + (3882627923/25000000000000 : ℝ)*(sp1) + (9136096033/50000000000000 : ℝ)*(sp2) + (678616779271103/25000000000000 : ℝ)*(sp4) + (1357224917325407/50000000000000 : ℝ)*(sp5) + (678611705570641/25000000000000 : ℝ)*(sp6) + (86290251075539/6250000000000 : ℝ)*(sp7) + (86290251075539/6250000000000 : ℝ)*(f.failure) + (678616779271103/25000000000000 : ℝ)*(f.sum) + (4216380732069/856000000000000000000000000 : ℝ)*base66 + (2474101685891697/684800000000000000000000000000 : ℝ)*base68 + (2151804520239503/684800000000000000000000000000 : ℝ)*base69 + (123194750813297/684800000000000000000000000000 : ℝ)*base72 + (670869873953/171200000000000000000000000 : ℝ)*base74 + (501584116240497/684800000000000000000000000000 : ℝ)*base76 + (2026499408098703/684800000000000000000000000000 : ℝ)*base77 + (730192564304497/684800000000000000000000000000 : ℝ)*base80 + (2109671198123/856000000000000000000000000 : ℝ)*base81 + (152161/78125000000000000000 : ℝ)*base89 + (152161/78125000000000000000 : ℝ)*base91 + (152161/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1082_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4143/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16689/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1082_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1082_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16689/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1082_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1082_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1082_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16689/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1082_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
