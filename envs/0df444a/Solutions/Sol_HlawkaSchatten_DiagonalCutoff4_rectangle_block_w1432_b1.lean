-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1432_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:03.094051+00:00
-- url     : https://prove2.me/submissions/5153ed23-6484-4e60-bd53-14b06c2afa87

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
theorem support_rectangle_w1432_s3_0 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1967662233/10000000000 : ℝ)*x 0 + (1083395629/2000000000 : ℝ)*x 1 + (2619371087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1967662233/10000000000 : ℝ)^549 ≤ (3000714608223/25000000000000 : ℝ)^421 := by
    have hnat : (1967662233 : ℕ)^549*25000000000000^421 ≤ 3000714608223^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967662233 10000000000 3000714608223 25000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083395629/2000000000 : ℝ)^549 ≤ (44958221045347/100000000000000 : ℝ)^421 := by
    have hnat : (1083395629 : ℕ)^549*100000000000000^421 ≤ 44958221045347^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083395629 2000000000 44958221045347 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619371087/5000000000 : ℝ)^549 ≤ (43038920513093/100000000000000 : ℝ)^421 := by
    have hnat : (2619371087 : ℕ)^549*100000000000000^421 ≤ 43038920513093^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619371087 5000000000 43038920513093 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1967662233/10000000000 : ℝ), (1083395629/2000000000 : ℝ), (2619371087/5000000000 : ℝ)] ![(3000714608223/25000000000000 : ℝ), (44958221045347/100000000000000 : ℝ), (43038920513093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1967662233/10000000000 : ℝ)|^549 ≤ (3000714608223/25000000000000 : ℝ)^421
        have hw : |(-1967662233/10000000000 : ℝ)|=(1967662233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083395629/2000000000 : ℝ)|^549 ≤ (44958221045347/100000000000000 : ℝ)^421
        have hw : |(1083395629/2000000000 : ℝ)|=(1083395629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619371087/5000000000 : ℝ)|^549 ≤ (43038920513093/100000000000000 : ℝ)^421
        have hw : |(2619371087/5000000000 : ℝ)|=(2619371087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s3_1 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5349565783/10000000000 : ℝ)*x 0 + (-2058575027/10000000000 : ℝ)*x 1 + (5238742139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349565783/10000000000 : ℝ)^549 ≤ (44230010351191/100000000000000 : ℝ)^421 := by
    have hnat : (5349565783 : ℕ)^549*100000000000000^421 ≤ 44230010351191^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349565783 10000000000 44230010351191 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058575027/10000000000 : ℝ)^549 ≤ (2546213900101/20000000000000 : ℝ)^421 := by
    have hnat : (2058575027 : ℕ)^549*20000000000000^421 ≤ 2546213900101^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058575027 10000000000 2546213900101 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238742139/10000000000 : ℝ)^549 ≤ (21519460069063/50000000000000 : ℝ)^421 := by
    have hnat : (5238742139 : ℕ)^549*50000000000000^421 ≤ 21519460069063^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238742139 10000000000 21519460069063 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349565783/10000000000 : ℝ), (-2058575027/10000000000 : ℝ), (5238742139/10000000000 : ℝ)] ![(44230010351191/100000000000000 : ℝ), (2546213900101/20000000000000 : ℝ), (21519460069063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349565783/10000000000 : ℝ)|^549 ≤ (44230010351191/100000000000000 : ℝ)^421
        have hw : |(5349565783/10000000000 : ℝ)|=(5349565783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058575027/10000000000 : ℝ)|^549 ≤ (2546213900101/20000000000000 : ℝ)^421
        have hw : |(-2058575027/10000000000 : ℝ)|=(2058575027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238742139/10000000000 : ℝ)|^549 ≤ (21519460069063/50000000000000 : ℝ)^421
        have hw : |(5238742139/10000000000 : ℝ)|=(5238742139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s3_2 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5349565817/10000000000 : ℝ)*x 0 + (5238742039/10000000000 : ℝ)*x 1 + (-1029287557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349565817/10000000000 : ℝ)^549 ≤ (4423001071777/10000000000000 : ℝ)^421 := by
    have hnat : (5349565817 : ℕ)^549*10000000000000^421 ≤ 4423001071777^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349565817 10000000000 4423001071777 10000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238742039/10000000000 : ℝ)^549 ≤ (43038919066793/100000000000000 : ℝ)^421 := by
    have hnat : (5238742039 : ℕ)^549*100000000000000^421 ≤ 43038919066793^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238742039 10000000000 43038919066793 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029287557/5000000000 : ℝ)^549 ≤ (6365535101067/50000000000000 : ℝ)^421 := by
    have hnat : (1029287557 : ℕ)^549*50000000000000^421 ≤ 6365535101067^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029287557 5000000000 6365535101067 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349565817/10000000000 : ℝ), (5238742039/10000000000 : ℝ), (-1029287557/5000000000 : ℝ)] ![(4423001071777/10000000000000 : ℝ), (43038919066793/100000000000000 : ℝ), (6365535101067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349565817/10000000000 : ℝ)|^549 ≤ (4423001071777/10000000000000 : ℝ)^421
        have hw : |(5349565817/10000000000 : ℝ)|=(5349565817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238742039/10000000000 : ℝ)|^549 ≤ (43038919066793/100000000000000 : ℝ)^421
        have hw : |(5238742039/10000000000 : ℝ)|=(5238742039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1029287557/5000000000 : ℝ)|^549 ≤ (6365535101067/50000000000000 : ℝ)^421
        have hw : |(-1029287557/5000000000 : ℝ)|=(1029287557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s3_3 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4302988959/10000000000 : ℝ)*x 0 + (1028468057/2500000000 : ℝ)*x 1 + (4499879597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302988959/10000000000 : ℝ)^549 ≤ (33298330818899/100000000000000 : ℝ)^421 := by
    have hnat : (4302988959 : ℕ)^549*100000000000000^421 ≤ 33298330818899^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302988959 10000000000 33298330818899 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028468057/2500000000 : ℝ)^549 ≤ (15701400296999/50000000000000 : ℝ)^421 := by
    have hnat : (1028468057 : ℕ)^549*50000000000000^421 ≤ 15701400296999^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028468057 2500000000 15701400296999 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499879597/10000000000 : ℝ)^549 ≤ (17649434282399/50000000000000 : ℝ)^421 := by
    have hnat : (4499879597 : ℕ)^549*50000000000000^421 ≤ 17649434282399^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499879597 10000000000 17649434282399 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302988959/10000000000 : ℝ), (1028468057/2500000000 : ℝ), (4499879597/10000000000 : ℝ)] ![(33298330818899/100000000000000 : ℝ), (15701400296999/50000000000000 : ℝ), (17649434282399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302988959/10000000000 : ℝ)|^549 ≤ (33298330818899/100000000000000 : ℝ)^421
        have hw : |(4302988959/10000000000 : ℝ)|=(4302988959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028468057/2500000000 : ℝ)|^549 ≤ (15701400296999/50000000000000 : ℝ)^421
        have hw : |(1028468057/2500000000 : ℝ)|=(1028468057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499879597/10000000000 : ℝ)|^549 ≤ (17649434282399/50000000000000 : ℝ)^421
        have hw : |(4499879597/10000000000 : ℝ)|=(4499879597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s3_4 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1967677143/10000000000 : ℝ)*x 0 + (81866457/156250000 : ℝ)*x 1 + (5416263279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1967677143/10000000000 : ℝ)^549 ≤ (12002977037763/100000000000000 : ℝ)^421 := by
    have hnat : (1967677143 : ℕ)^549*100000000000000^421 ≤ 12002977037763^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967677143 10000000000 12002977037763 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81866457/156250000 : ℝ)^549 ≤ (538081733033/1250000000000 : ℝ)^421 := by
    have hnat : (81866457 : ℕ)^549*1250000000000^421 ≤ 538081733033^421*156250000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81866457 156250000 538081733033 1250000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416263279/10000000000 : ℝ)^549 ≤ (44950484301603/100000000000000 : ℝ)^421 := by
    have hnat : (5416263279 : ℕ)^549*100000000000000^421 ≤ 44950484301603^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416263279 10000000000 44950484301603 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1967677143/10000000000 : ℝ), (81866457/156250000 : ℝ), (5416263279/10000000000 : ℝ)] ![(12002977037763/100000000000000 : ℝ), (538081733033/1250000000000 : ℝ), (44950484301603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1967677143/10000000000 : ℝ)|^549 ≤ (12002977037763/100000000000000 : ℝ)^421
        have hw : |(-1967677143/10000000000 : ℝ)|=(1967677143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81866457/156250000 : ℝ)|^549 ≤ (538081733033/1250000000000 : ℝ)^421
        have hw : |(81866457/156250000 : ℝ)|=(81866457/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416263279/10000000000 : ℝ)|^549 ≤ (44950484301603/100000000000000 : ℝ)^421
        have hw : |(5416263279/10000000000 : ℝ)|=(5416263279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s3_5 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5303216449/10000000000 : ℝ)*x 0 + (-1881053969/10000000000 : ℝ)*x 1 + (5416263237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303216449/10000000000 : ℝ)^549 ≤ (43730943518539/100000000000000 : ℝ)^421 := by
    have hnat : (5303216449 : ℕ)^549*100000000000000^421 ≤ 43730943518539^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303216449 10000000000 43730943518539 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1881053969/10000000000 : ℝ)^549 ≤ (11318572619871/100000000000000 : ℝ)^421 := by
    have hnat : (1881053969 : ℕ)^549*100000000000000^421 ≤ 11318572619871^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881053969 10000000000 11318572619871 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416263237/10000000000 : ℝ)^549 ≤ (44950483847061/100000000000000 : ℝ)^421 := by
    have hnat : (5416263237 : ℕ)^549*100000000000000^421 ≤ 44950483847061^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416263237 10000000000 44950483847061 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303216449/10000000000 : ℝ), (-1881053969/10000000000 : ℝ), (5416263237/10000000000 : ℝ)] ![(43730943518539/100000000000000 : ℝ), (11318572619871/100000000000000 : ℝ), (44950483847061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303216449/10000000000 : ℝ)|^549 ≤ (43730943518539/100000000000000 : ℝ)^421
        have hw : |(5303216449/10000000000 : ℝ)|=(5303216449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1881053969/10000000000 : ℝ)|^549 ≤ (11318572619871/100000000000000 : ℝ)^421
        have hw : |(-1881053969/10000000000 : ℝ)|=(1881053969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416263237/10000000000 : ℝ)|^549 ≤ (44950483847061/100000000000000 : ℝ)^421
        have hw : |(5416263237/10000000000 : ℝ)|=(5416263237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s3_6 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5303216133/10000000000 : ℝ)*x 0 + (5416263571/10000000000 : ℝ)*x 1 + (-1881053941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303216133/10000000000 : ℝ)^549 ≤ (683295939383/1562500000000 : ℝ)^421 := by
    have hnat : (5303216133 : ℕ)^549*1562500000000^421 ≤ 683295939383^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303216133 10000000000 683295939383 1562500000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416263571/10000000000 : ℝ)^549 ≤ (22475243730877/50000000000000 : ℝ)^421 := by
    have hnat : (5416263571 : ℕ)^549*50000000000000^421 ≤ 22475243730877^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416263571 10000000000 22475243730877 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1881053941/10000000000 : ℝ)^549 ≤ (11318572400167/100000000000000 : ℝ)^421 := by
    have hnat : (1881053941 : ℕ)^549*100000000000000^421 ≤ 11318572400167^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881053941 10000000000 11318572400167 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303216133/10000000000 : ℝ), (5416263571/10000000000 : ℝ), (-1881053941/10000000000 : ℝ)] ![(683295939383/1562500000000 : ℝ), (22475243730877/50000000000000 : ℝ), (11318572400167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303216133/10000000000 : ℝ)|^549 ≤ (683295939383/1562500000000 : ℝ)^421
        have hw : |(5303216133/10000000000 : ℝ)|=(5303216133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416263571/10000000000 : ℝ)|^549 ≤ (22475243730877/50000000000000 : ℝ)^421
        have hw : |(5416263571/10000000000 : ℝ)|=(5416263571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1881053941/10000000000 : ℝ)|^549 ≤ (11318572400167/100000000000000 : ℝ)^421
        have hw : |(-1881053941/10000000000 : ℝ)|=(1881053941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s3_7 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (107575543/250000000 : ℝ)*x 0 + (112458509/250000000 : ℝ)*x 1 + (514427579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107575543/250000000 : ℝ)^549 ≤ (33298661416831/100000000000000 : ℝ)^421 := by
    have hnat : (107575543 : ℕ)^549*100000000000000^421 ≤ 33298661416831^421*250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107575543 250000000 33298661416831 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112458509/250000000 : ℝ)^549 ≤ (35283123913417/100000000000000 : ℝ)^421 := by
    have hnat : (112458509 : ℕ)^549*100000000000000^421 ≤ 35283123913417^421*250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112458509 250000000 35283123913417 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514427579/1250000000 : ℝ)^549 ≤ (6283642930211/20000000000000 : ℝ)^421 := by
    have hnat : (514427579 : ℕ)^549*20000000000000^421 ≤ 6283642930211^421*1250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514427579 1250000000 6283642930211 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107575543/250000000 : ℝ), (112458509/250000000 : ℝ), (514427579/1250000000 : ℝ)] ![(33298661416831/100000000000000 : ℝ), (35283123913417/100000000000000 : ℝ), (6283642930211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107575543/250000000 : ℝ)|^549 ≤ (33298661416831/100000000000000 : ℝ)^421
        have hw : |(107575543/250000000 : ℝ)|=(107575543/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112458509/250000000 : ℝ)|^549 ≤ (35283123913417/100000000000000 : ℝ)^421
        have hw : |(112458509/250000000 : ℝ)|=(112458509/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514427579/1250000000 : ℝ)|^549 ≤ (6283642930211/20000000000000 : ℝ)^421
        have hw : |(514427579/1250000000 : ℝ)|=(514427579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1432_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1579/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1117/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2989/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1579/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1579/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1579/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1579/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1579/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1579/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10383/100000 : ℝ) ^ (4391/1024 : ℝ) ≤ (6052124636794147/100000000000000000000 : ℝ) := by
    have hpowers : (10383/100000 : ℝ)^4391 ≤ (6052124636794147/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10383 : ℕ)^4391*100000000000000000000^1024 ≤ 6052124636794147^1024*100000^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10383 100000 6052124636794147 100000000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10383/100000 : ℝ)) (X := (6052124636794147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1579/10000 : ℝ) ^ (4391/1024 : ℝ) ≤ (36525290979803517/100000000000000000000 : ℝ) := by
    have hpowers : (1579/10000 : ℝ)^4391 ≤ (36525290979803517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1579 : ℕ)^4391*100000000000000000000^1024 ≤ 36525290979803517^1024*10000^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1579 10000 36525290979803517 100000000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1579/10000 : ℝ)) (X := (36525290979803517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006052124636794147/50000000000000000000 : ℝ) ≤ (10000282263176693/10000000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (50006052124636794147/50000000000000000000 : ℝ)^1024 ≤ (10000282263176693/10000000000000000 : ℝ)^4391 := by
      have hnat : (50006052124636794147 : ℕ)^1024*10000000000000000^4391 ≤ 10000282263176693^4391*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006052124636794147 50000000000000000000 10000282263176693 10000000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282263176693/10000000000000000 : ℝ)) (X := (50006052124636794147/50000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126330544238018677/3125000000000000000 : ℝ) ≤ (10000992761516531/10000000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (3126330544238018677/3125000000000000000 : ℝ)^1024 ≤ (10000992761516531/10000000000000000 : ℝ)^4391 := by
      have hnat : (3126330544238018677 : ℕ)^1024*10000000000000000^4391 ≤ 10000992761516531^4391*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126330544238018677 3125000000000000000 10000992761516531 10000000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000992761516531/10000000000000000 : ℝ)) (X := (3126330544238018677/3125000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036525290979803517/50000000000000000000 : ℝ) ≤ (10001703259856369/10000000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (50036525290979803517/50000000000000000000 : ℝ)^1024 ≤ (10001703259856369/10000000000000000 : ℝ)^4391 := by
      have hnat : (50036525290979803517 : ℕ)^1024*10000000000000000^4391 ≤ 10001703259856369^4391*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036525290979803517 50000000000000000000 10001703259856369 10000000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001703259856369/10000000000000000 : ℝ)) (X := (50036525290979803517/50000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6052124636794147/100000000000000000000 : ℝ) ≤ ((54056771988471303143/54070000000000000000 : ℝ)+2*(355249169919/270350000000000 : ℝ)*(10383/100000 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (54056771988471303143/54070000000000000000 : ℝ)+2*(355249169919/270350000000000 : ℝ)*(10383/100000 : ℝ)=(10000282263176693/10000000000000000 : ℝ) by norm_num, show 1+2*(6052124636794147/100000000000000000000 : ℝ)=(50006052124636794147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36525290979803517/100000000000000000000 : ℝ)+(6052124636794147/100000000000000000000 : ℝ) ≤ ((54056771988471303143/54070000000000000000 : ℝ)+(355249169919/270350000000000 : ℝ)*((1579/10000 : ℝ)+(10383/100000 : ℝ)))^(4391/1024 : ℝ) := by
    rw [show (54056771988471303143/54070000000000000000 : ℝ)+(355249169919/270350000000000 : ℝ)*((1579/10000 : ℝ)+(10383/100000 : ℝ))=(10000992761516531/10000000000000000 : ℝ) by norm_num, show 1+(36525290979803517/100000000000000000000 : ℝ)+(6052124636794147/100000000000000000000 : ℝ)=(3126330544238018677/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36525290979803517/100000000000000000000 : ℝ) ≤ ((54056771988471303143/54070000000000000000 : ℝ)+2*(355249169919/270350000000000 : ℝ)*(1579/10000 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (54056771988471303143/54070000000000000000 : ℝ)+2*(355249169919/270350000000000 : ℝ)*(1579/10000 : ℝ)=(10001703259856369/10000000000000000 : ℝ) by norm_num, show 1+2*(36525290979803517/100000000000000000000 : ℝ)=(50036525290979803517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54056771988471303143/54070000000000000000 : ℝ)*(X 1 0+X 2 0)+(355249169919/270350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (10383/100000 : ℝ)) (hi := (1579/10000 : ℝ)) (c := (54056771988471303143/54070000000000000000 : ℝ)) (alpha := (355249169919/270350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54056771988471303143/54070000000000000000 : ℝ)*(X 0 1+X 2 1)+(355249169919/270350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (10383/100000 : ℝ)) (hi := (1579/10000 : ℝ)) (c := (54056771988471303143/54070000000000000000 : ℝ)) (alpha := (355249169919/270350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54056771988471303143/54070000000000000000 : ℝ)*(X 0 2+X 1 2)+(355249169919/270350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (10383/100000 : ℝ)) (hi := (1579/10000 : ℝ)) (c := (54056771988471303143/54070000000000000000 : ℝ)) (alpha := (355249169919/270350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1967662233/10000000000 : ℝ)*X 0 0+(1083395629/2000000000 : ℝ)*X 0 1+(2619371087/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349565783/10000000000 : ℝ)*X 1 0+(-2058575027/10000000000 : ℝ)*X 1 1+(5238742139/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349565817/10000000000 : ℝ)*X 2 0+(5238742039/10000000000 : ℝ)*X 2 1+(-1029287557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302988959/10000000000 : ℝ)*X 0 0+(1028468057/2500000000 : ℝ)*X 0 1+(4499879597/10000000000 : ℝ)*X 0 2+(4302988959/10000000000 : ℝ)*X 1 0+(1028468057/2500000000 : ℝ)*X 1 1+(4499879597/10000000000 : ℝ)*X 1 2+(4302988959/10000000000 : ℝ)*X 2 0+(1028468057/2500000000 : ℝ)*X 2 1+(4499879597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1967677143/10000000000 : ℝ)*X 0 0+(81866457/156250000 : ℝ)*X 0 1+(5416263279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303216449/10000000000 : ℝ)*X 1 0+(-1881053969/10000000000 : ℝ)*X 1 1+(5416263237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303216133/10000000000 : ℝ)*X 2 0+(5416263571/10000000000 : ℝ)*X 2 1+(-1881053941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((107575543/250000000 : ℝ)*X 0 0+(112458509/250000000 : ℝ)*X 0 1+(514427579/1250000000 : ℝ)*X 0 2+(107575543/250000000 : ℝ)*X 1 0+(112458509/250000000 : ℝ)*X 1 1+(514427579/1250000000 : ℝ)*X 1 2+(107575543/250000000 : ℝ)*X 2 0+(112458509/250000000 : ℝ)*X 2 1+(514427579/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58198514796037441673163/5407000000000000000000000000 : ℝ) := by norm_num
    linear_combination (931607061/50000000000000 : ℝ)*(base19) + (74226367/4000000000000 : ℝ)*(base23) + (325456467/100000000000000 : ℝ)*(upper3) + (1444851/6250000000000 : ℝ)*(upper4) + (199081521/100000000000000 : ℝ)*(upper5) + (102515691921661/2500000000000 : ℝ)*(major0) + (102515691921661/2500000000000 : ℝ)*(major1) + (102515691921661/2500000000000 : ℝ)*(major2) + (561057377870027/10000000000000 : ℝ)*(sp0) + (5610602448796861/100000000000000 : ℝ)*(sp1) + (87665663380497/1562500000000 : ℝ)*(sp2) + (129531817941551/5000000000000 : ℝ)*(sp3) + (30533310713/100000000000000 : ℝ)*(sp4) + (1432410587/10000000000000 : ℝ)*(sp7) + (2590650682936891/100000000000000 : ℝ)*(f.failure) + (5610604312010983/100000000000000 : ℝ)*(f.sum) + (46493078226967/5407000000000000000000000000 : ℝ)*base65 + (430913421837569477/135175000000000000000000000000000 : ℝ)*base68 + (327562566240655523/135175000000000000000000000000000 : ℝ)*base69 + (2307848192270855523/135175000000000000000000000000000 : ℝ)*base71 + (3267903971447/5407000000000000000000000000 : ℝ)*base74 + (631940778364444477/135175000000000000000000000000000 : ℝ)*base76 + (1026451376420580523/135175000000000000000000000000000 : ℝ)*base77 + (785965636486719477/135175000000000000000000000000000 : ℝ)*base80 + (53328019633/1351750000000000000000000000 : ℝ)*base82 + (6634343/10000000000000000000000 : ℝ)*base90 + (6634343/10000000000000000000000 : ℝ)*base92 + (6634343/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6189544921893462194444918277/675875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (533352711/100000000000000 : ℝ)*(base19) + (388720391/100000000000000 : ℝ)*(base23) + (232523/312500000000 : ℝ)*(upper3) + (11049391/12500000000000 : ℝ)*(lower4) + (71658433/100000000000000 : ℝ)*(upper5) + (2066823921248313/50000000000000 : ℝ)*(major0) + (2066823921248313/50000000000000 : ℝ)*(major1) + (2066823921248313/50000000000000 : ℝ)*(major2) + (4121008507/50000000000000 : ℝ)*(sp1) + (11181774229/100000000000000 : ℝ)*(sp2) + (5655783569821443/100000000000000 : ℝ)*(sp4) + (5655774794451717/100000000000000 : ℝ)*(sp5) + (706971499915853/12500000000000 : ℝ)*(sp6) + (261151180991097/10000000000000 : ℝ)*(sp7) + (261151180991097/10000000000000 : ℝ)*(f.failure) + (5655783569821443/100000000000000 : ℝ)*(f.sum) + (104758728177197/27035000000000000000000000000 : ℝ)*base66 + (21504195093705747759/2703500000000000000000000000000000 : ℝ)*base67 + (7693817328399752241/2703500000000000000000000000000000 : ℝ)*base70 + (1424316095302752241/2703500000000000000000000000000000 : ℝ)*base72 + (66710588313127/27035000000000000000000000000 : ℝ)*base74 + (17555345291472752241/2703500000000000000000000000000000 : ℝ)*base76 + (19044260527067752241/2703500000000000000000000000000000 : ℝ)*base78 + (40992734903992752241/2703500000000000000000000000000000 : ℝ)*base80 + (66019758426331/13517500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (10062819/1000000000000000000000 : ℝ)*base89 + (10062819/1000000000000000000000 : ℝ)*base91 + (10062819/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1432_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1579/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2989/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1432_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1432_s4_0 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-393709433/2000000000 : ℝ)*x 0 + (1081882197/2000000000 : ℝ)*x 1 + (5245726549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393709433/2000000000 : ℝ)^549 ≤ (750618643253/6250000000000 : ℝ)^421 := by
    have hnat : (393709433 : ℕ)^549*6250000000000^421 ≤ 750618643253^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393709433 2000000000 750618643253 6250000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081882197/2000000000 : ℝ)^549 ≤ (44876340083889/100000000000000 : ℝ)^421 := by
    have hnat : (1081882197 : ℕ)^549*100000000000000^421 ≤ 44876340083889^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081882197 2000000000 44876340083889 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245726549/10000000000 : ℝ)^549 ≤ (43113761607023/100000000000000 : ℝ)^421 := by
    have hnat : (5245726549 : ℕ)^549*100000000000000^421 ≤ 43113761607023^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245726549 10000000000 43113761607023 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393709433/2000000000 : ℝ), (1081882197/2000000000 : ℝ), (5245726549/10000000000 : ℝ)] ![(750618643253/6250000000000 : ℝ), (44876340083889/100000000000000 : ℝ), (43113761607023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393709433/2000000000 : ℝ)|^549 ≤ (750618643253/6250000000000 : ℝ)^421
        have hw : |(-393709433/2000000000 : ℝ)|=(393709433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081882197/2000000000 : ℝ)|^549 ≤ (44876340083889/100000000000000 : ℝ)^421
        have hw : |(1081882197/2000000000 : ℝ)|=(1081882197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245726549/10000000000 : ℝ)|^549 ≤ (43113761607023/100000000000000 : ℝ)^421
        have hw : |(5245726549/10000000000 : ℝ)|=(5245726549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s4_1 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1336902983/2500000000 : ℝ)*x 0 + (-128243953/625000000 : ℝ)*x 1 + (5245726797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336902983/2500000000 : ℝ)^549 ≤ (44208945612171/100000000000000 : ℝ)^421 := by
    have hnat : (1336902983 : ℕ)^549*100000000000000^421 ≤ 44208945612171^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336902983 2500000000 44208945612171 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128243953/625000000 : ℝ)^549 ≤ (6338645053281/50000000000000 : ℝ)^421 := by
    have hnat : (128243953 : ℕ)^549*50000000000000^421 ≤ 6338645053281^421*625000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128243953 625000000 6338645053281 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245726797/10000000000 : ℝ)^549 ≤ (21556882132503/50000000000000 : ℝ)^421 := by
    have hnat : (5245726797 : ℕ)^549*50000000000000^421 ≤ 21556882132503^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245726797 10000000000 21556882132503 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336902983/2500000000 : ℝ), (-128243953/625000000 : ℝ), (5245726797/10000000000 : ℝ)] ![(44208945612171/100000000000000 : ℝ), (6338645053281/50000000000000 : ℝ), (21556882132503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336902983/2500000000 : ℝ)|^549 ≤ (44208945612171/100000000000000 : ℝ)^421
        have hw : |(1336902983/2500000000 : ℝ)|=(1336902983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128243953/625000000 : ℝ)|^549 ≤ (6338645053281/50000000000000 : ℝ)^421
        have hw : |(-128243953/625000000 : ℝ)|=(128243953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245726797/10000000000 : ℝ)|^549 ≤ (21556882132503/50000000000000 : ℝ)^421
        have hw : |(5245726797/10000000000 : ℝ)|=(5245726797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s4_2 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347611903/10000000000 : ℝ)*x 0 + (1311431711/2500000000 : ℝ)*x 1 + (-256487903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347611903/10000000000 : ℝ)^549 ≤ (8841789059907/20000000000000 : ℝ)^421 := by
    have hnat : (5347611903 : ℕ)^549*20000000000000^421 ≤ 8841789059907^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347611903 10000000000 8841789059907 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311431711/2500000000 : ℝ)^549 ≤ (1347305149023/3125000000000 : ℝ)^421 := by
    have hnat : (1311431711 : ℕ)^549*3125000000000^421 ≤ 1347305149023^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311431711 2500000000 1347305149023 3125000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256487903/1250000000 : ℝ)^549 ≤ (31693224783/250000000000 : ℝ)^421 := by
    have hnat : (256487903 : ℕ)^549*250000000000^421 ≤ 31693224783^421*1250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256487903 1250000000 31693224783 250000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347611903/10000000000 : ℝ), (1311431711/2500000000 : ℝ), (-256487903/1250000000 : ℝ)] ![(8841789059907/20000000000000 : ℝ), (1347305149023/3125000000000 : ℝ), (31693224783/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347611903/10000000000 : ℝ)|^549 ≤ (8841789059907/20000000000000 : ℝ)^421
        have hw : |(5347611903/10000000000 : ℝ)|=(5347611903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311431711/2500000000 : ℝ)|^549 ≤ (1347305149023/3125000000000 : ℝ)^421
        have hw : |(1311431711/2500000000 : ℝ)|=(1311431711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256487903/1250000000 : ℝ)|^549 ≤ (31693224783/250000000000 : ℝ)^421
        have hw : |(-256487903/1250000000 : ℝ)|=(256487903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s4_3 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (67242683/156250000 : ℝ)*x 0 + (412956407/1000000000 : ℝ)*x 1 + (4484057117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67242683/156250000 : ℝ)^549 ≤ (3330380794879/10000000000000 : ℝ)^421 := by
    have hnat : (67242683 : ℕ)^549*10000000000000^421 ≤ 3330380794879^421*156250000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67242683 156250000 3330380794879 10000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412956407/1000000000 : ℝ)^549 ≤ (3944886418717/12500000000000 : ℝ)^421 := by
    have hnat : (412956407 : ℕ)^549*12500000000000^421 ≤ 3944886418717^421*1000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412956407 1000000000 3944886418717 12500000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484057117/10000000000 : ℝ)^549 ≤ (17568550341159/50000000000000 : ℝ)^421 := by
    have hnat : (4484057117 : ℕ)^549*50000000000000^421 ≤ 17568550341159^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484057117 10000000000 17568550341159 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67242683/156250000 : ℝ), (412956407/1000000000 : ℝ), (4484057117/10000000000 : ℝ)] ![(3330380794879/10000000000000 : ℝ), (3944886418717/12500000000000 : ℝ), (17568550341159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67242683/156250000 : ℝ)|^549 ≤ (3330380794879/10000000000000 : ℝ)^421
        have hw : |(67242683/156250000 : ℝ)|=(67242683/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(412956407/1000000000 : ℝ)|^549 ≤ (3944886418717/12500000000000 : ℝ)^421
        have hw : |(412956407/1000000000 : ℝ)|=(412956407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484057117/10000000000 : ℝ)|^549 ≤ (17568550341159/50000000000000 : ℝ)^421
        have hw : |(4484057117/10000000000 : ℝ)|=(4484057117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s4_4 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-98427951/500000000 : ℝ)*x 0 + (2623163311/5000000000 : ℝ)*x 1 + (2704403877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98427951/500000000 : ℝ)^549 ≤ (12009992608121/100000000000000 : ℝ)^421 := by
    have hnat : (98427951 : ℕ)^549*100000000000000^421 ≤ 12009992608121^421*500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98427951 500000000 12009992608121 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623163311/5000000000 : ℝ)^549 ≤ (2695012069079/6250000000000 : ℝ)^421 := by
    have hnat : (2623163311 : ℕ)^549*6250000000000^421 ≤ 2695012069079^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623163311 5000000000 2695012069079 6250000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704403877/5000000000 : ℝ)^549 ≤ (44869814280431/100000000000000 : ℝ)^421 := by
    have hnat : (2704403877 : ℕ)^549*100000000000000^421 ≤ 44869814280431^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704403877 5000000000 44869814280431 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98427951/500000000 : ℝ), (2623163311/5000000000 : ℝ), (2704403877/5000000000 : ℝ)] ![(12009992608121/100000000000000 : ℝ), (2695012069079/6250000000000 : ℝ), (44869814280431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98427951/500000000 : ℝ)|^549 ≤ (12009992608121/100000000000000 : ℝ)^421
        have hw : |(-98427951/500000000 : ℝ)|=(98427951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623163311/5000000000 : ℝ)|^549 ≤ (2695012069079/6250000000000 : ℝ)^421
        have hw : |(2623163311/5000000000 : ℝ)|=(2623163311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704403877/5000000000 : ℝ)|^549 ≤ (44869814280431/100000000000000 : ℝ)^421
        have hw : |(2704403877/5000000000 : ℝ)|=(2704403877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s4_5 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1061009263/2000000000 : ℝ)*x 0 + (-377764419/2000000000 : ℝ)*x 1 + (2704403879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061009263/2000000000 : ℝ)^549 ≤ (1750024862287/4000000000000 : ℝ)^421 := by
    have hnat : (1061009263 : ℕ)^549*4000000000000^421 ≤ 1750024862287^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061009263 2000000000 1750024862287 4000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377764419/2000000000 : ℝ)^549 ≤ (11379564105801/100000000000000 : ℝ)^421 := by
    have hnat : (377764419 : ℕ)^549*100000000000000^421 ≤ 11379564105801^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377764419 2000000000 11379564105801 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704403879/5000000000 : ℝ)^549 ≤ (22434907161851/50000000000000 : ℝ)^421 := by
    have hnat : (2704403879 : ℕ)^549*50000000000000^421 ≤ 22434907161851^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704403879 5000000000 22434907161851 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061009263/2000000000 : ℝ), (-377764419/2000000000 : ℝ), (2704403879/5000000000 : ℝ)] ![(1750024862287/4000000000000 : ℝ), (11379564105801/100000000000000 : ℝ), (22434907161851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061009263/2000000000 : ℝ)|^549 ≤ (1750024862287/4000000000000 : ℝ)^421
        have hw : |(1061009263/2000000000 : ℝ)|=(1061009263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-377764419/2000000000 : ℝ)|^549 ≤ (11379564105801/100000000000000 : ℝ)^421
        have hw : |(-377764419/2000000000 : ℝ)|=(377764419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704403879/5000000000 : ℝ)|^549 ≤ (22434907161851/50000000000000 : ℝ)^421
        have hw : |(2704403879/5000000000 : ℝ)|=(2704403879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s4_6 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305046301/10000000000 : ℝ)*x 0 + (5408807759/10000000000 : ℝ)*x 1 + (-1888822113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305046301/10000000000 : ℝ)^549 ≤ (43750621406613/100000000000000 : ℝ)^421 := by
    have hnat : (5305046301 : ℕ)^549*100000000000000^421 ≤ 43750621406613^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305046301 10000000000 43750621406613 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408807759/10000000000 : ℝ)^549 ≤ (1121745358363/2500000000000 : ℝ)^421 := by
    have hnat : (5408807759 : ℕ)^549*2500000000000^421 ≤ 1121745358363^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408807759 10000000000 1121745358363 2500000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1888822113/10000000000 : ℝ)^549 ≤ (11379564247217/100000000000000 : ℝ)^421 := by
    have hnat : (1888822113 : ℕ)^549*100000000000000^421 ≤ 11379564247217^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888822113 10000000000 11379564247217 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305046301/10000000000 : ℝ), (5408807759/10000000000 : ℝ), (-1888822113/10000000000 : ℝ)] ![(43750621406613/100000000000000 : ℝ), (1121745358363/2500000000000 : ℝ), (11379564247217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305046301/10000000000 : ℝ)|^549 ≤ (43750621406613/100000000000000 : ℝ)^421
        have hw : |(5305046301/10000000000 : ℝ)|=(5305046301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408807759/10000000000 : ℝ)|^549 ≤ (1121745358363/2500000000000 : ℝ)^421
        have hw : |(5408807759/10000000000 : ℝ)|=(5408807759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1888822113/10000000000 : ℝ)|^549 ≤ (11379564247217/100000000000000 : ℝ)^421
        have hw : |(-1888822113/10000000000 : ℝ)|=(1888822113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s4_7 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (268972341/625000000 : ℝ)*x 0 + (4482757727/10000000000 : ℝ)*x 1 + (516358777/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268972341/625000000 : ℝ)^549 ≤ (16652033873321/50000000000000 : ℝ)^421 := by
    have hnat : (268972341 : ℕ)^549*50000000000000^421 ≤ 16652033873321^421*625000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268972341 625000000 16652033873321 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482757727/10000000000 : ℝ)^549 ≤ (35123823515171/100000000000000 : ℝ)^421 := by
    have hnat : (4482757727 : ℕ)^549*100000000000000^421 ≤ 35123823515171^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482757727 10000000000 35123823515171 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516358777/1250000000 : ℝ)^549 ≤ (15786054358159/50000000000000 : ℝ)^421 := by
    have hnat : (516358777 : ℕ)^549*50000000000000^421 ≤ 15786054358159^421*1250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516358777 1250000000 15786054358159 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268972341/625000000 : ℝ), (4482757727/10000000000 : ℝ), (516358777/1250000000 : ℝ)] ![(16652033873321/50000000000000 : ℝ), (35123823515171/100000000000000 : ℝ), (15786054358159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268972341/625000000 : ℝ)|^549 ≤ (16652033873321/50000000000000 : ℝ)^421
        have hw : |(268972341/625000000 : ℝ)|=(268972341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482757727/10000000000 : ℝ)|^549 ≤ (35123823515171/100000000000000 : ℝ)^421
        have hw : |(4482757727/10000000000 : ℝ)|=(4482757727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516358777/1250000000 : ℝ)|^549 ≤ (15786054358159/50000000000000 : ℝ)^421
        have hw : |(516358777/1250000000 : ℝ)|=(516358777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1432_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2989/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (283/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14787/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2989/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1117/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2989/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1117/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2989/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1117/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2989/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1117/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2989/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1117/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2989/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1117/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1117/10000 : ℝ) ^ (4391/1024 : ℝ) ≤ (8278853516538781/100000000000000000000 : ℝ) := by
    have hpowers : (1117/10000 : ℝ)^4391 ≤ (8278853516538781/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1117 : ℕ)^4391*100000000000000000000^1024 ≤ 8278853516538781^1024*10000^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1117 10000 8278853516538781 100000000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1117/10000 : ℝ)) (X := (8278853516538781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2989/20000 : ℝ) ^ (4391/1024 : ℝ) ≤ (28851444416679631/100000000000000000000 : ℝ) := by
    have hpowers : (2989/20000 : ℝ)^4391 ≤ (28851444416679631/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2989 : ℕ)^4391*100000000000000000000^1024 ≤ 28851444416679631^1024*20000^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2989 20000 28851444416679631 100000000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2989/20000 : ℝ)) (X := (28851444416679631/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008278853516538781/50000000000000000000 : ℝ) ≤ (2500096527076779/2500000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (50008278853516538781/50000000000000000000 : ℝ)^1024 ≤ (2500096527076779/2500000000000000 : ℝ)^4391 := by
      have hnat : (50008278853516538781 : ℕ)^1024*2500000000000000^4391 ≤ 2500096527076779^4391*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008278853516538781 50000000000000000000 2500096527076779 2500000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500096527076779/2500000000000000 : ℝ)) (X := (50008278853516538781/50000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009282574483304603/25000000000000000000 : ℝ) ≤ (5000432885603049/5000000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (25009282574483304603/25000000000000000000 : ℝ)^1024 ≤ (5000432885603049/5000000000000000 : ℝ)^4391 := by
      have hnat : (25009282574483304603 : ℕ)^1024*5000000000000000^4391 ≤ 5000432885603049^4391*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009282574483304603 25000000000000000000 5000432885603049 5000000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000432885603049/5000000000000000 : ℝ)) (X := (25009282574483304603/25000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028851444416679631/50000000000000000000 : ℝ) ≤ (250033635852627/250000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (50028851444416679631/50000000000000000000 : ℝ)^1024 ≤ (250033635852627/250000000000000 : ℝ)^4391 := by
      have hnat : (50028851444416679631 : ℕ)^1024*250000000000000^4391 ≤ 250033635852627^4391*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028851444416679631 50000000000000000000 250033635852627 250000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250033635852627/250000000000000 : ℝ)) (X := (50028851444416679631/50000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8278853516538781/100000000000000000000 : ℝ) ≤ ((1887037094484805251/1887500000000000000 : ℝ)+2*(239831449491/188750000000000 : ℝ)*(1117/10000 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (1887037094484805251/1887500000000000000 : ℝ)+2*(239831449491/188750000000000 : ℝ)*(1117/10000 : ℝ)=(2500096527076779/2500000000000000 : ℝ) by norm_num, show 1+2*(8278853516538781/100000000000000000000 : ℝ)=(50008278853516538781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28851444416679631/100000000000000000000 : ℝ)+(8278853516538781/100000000000000000000 : ℝ) ≤ ((1887037094484805251/1887500000000000000 : ℝ)+(239831449491/188750000000000 : ℝ)*((2989/20000 : ℝ)+(1117/10000 : ℝ)))^(4391/1024 : ℝ) := by
    rw [show (1887037094484805251/1887500000000000000 : ℝ)+(239831449491/188750000000000 : ℝ)*((2989/20000 : ℝ)+(1117/10000 : ℝ))=(5000432885603049/5000000000000000 : ℝ) by norm_num, show 1+(28851444416679631/100000000000000000000 : ℝ)+(8278853516538781/100000000000000000000 : ℝ)=(25009282574483304603/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28851444416679631/100000000000000000000 : ℝ) ≤ ((1887037094484805251/1887500000000000000 : ℝ)+2*(239831449491/188750000000000 : ℝ)*(2989/20000 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (1887037094484805251/1887500000000000000 : ℝ)+2*(239831449491/188750000000000 : ℝ)*(2989/20000 : ℝ)=(250033635852627/250000000000000 : ℝ) by norm_num, show 1+2*(28851444416679631/100000000000000000000 : ℝ)=(50028851444416679631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1887037094484805251/1887500000000000000 : ℝ)*(X 1 0+X 2 0)+(239831449491/188750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (2989/20000 : ℝ)) (c := (1887037094484805251/1887500000000000000 : ℝ)) (alpha := (239831449491/188750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1887037094484805251/1887500000000000000 : ℝ)*(X 0 1+X 2 1)+(239831449491/188750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (2989/20000 : ℝ)) (c := (1887037094484805251/1887500000000000000 : ℝ)) (alpha := (239831449491/188750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1887037094484805251/1887500000000000000 : ℝ)*(X 0 2+X 1 2)+(239831449491/188750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (2989/20000 : ℝ)) (c := (1887037094484805251/1887500000000000000 : ℝ)) (alpha := (239831449491/188750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-393709433/2000000000 : ℝ)*X 0 0+(1081882197/2000000000 : ℝ)*X 0 1+(5245726549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336902983/2500000000 : ℝ)*X 1 0+(-128243953/625000000 : ℝ)*X 1 1+(5245726797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347611903/10000000000 : ℝ)*X 2 0+(1311431711/2500000000 : ℝ)*X 2 1+(-256487903/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((67242683/156250000 : ℝ)*X 0 0+(412956407/1000000000 : ℝ)*X 0 1+(4484057117/10000000000 : ℝ)*X 0 2+(67242683/156250000 : ℝ)*X 1 0+(412956407/1000000000 : ℝ)*X 1 1+(4484057117/10000000000 : ℝ)*X 1 2+(67242683/156250000 : ℝ)*X 2 0+(412956407/1000000000 : ℝ)*X 2 1+(4484057117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-98427951/500000000 : ℝ)*X 0 0+(2623163311/5000000000 : ℝ)*X 0 1+(2704403877/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061009263/2000000000 : ℝ)*X 1 0+(-377764419/2000000000 : ℝ)*X 1 1+(2704403879/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305046301/10000000000 : ℝ)*X 2 0+(5408807759/10000000000 : ℝ)*X 2 1+(-1888822113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((268972341/625000000 : ℝ)*X 0 0+(4482757727/10000000000 : ℝ)*X 0 1+(516358777/1250000000 : ℝ)*X 0 2+(268972341/625000000 : ℝ)*X 1 0+(4482757727/10000000000 : ℝ)*X 1 1+(516358777/1250000000 : ℝ)*X 1 2+(268972341/625000000 : ℝ)*X 2 0+(4482757727/10000000000 : ℝ)*X 2 1+(516358777/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18587103880527328775918511/5898437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5671389/6250000000000 : ℝ)*(base19) + (54968521/100000000000000 : ℝ)*(base23) + (1413317/100000000000000 : ℝ)*(lower2) + (36907071/100000000000000 : ℝ)*(upper3) + (29732081/50000000000000 : ℝ)*(upper5) + (1116283801130951/25000000000000 : ℝ)*(major0) + (1116283801130951/25000000000000 : ℝ)*(major1) + (1116283801130951/25000000000000 : ℝ)*(major2) + (610932528211269/10000000000000 : ℝ)*(sp0) + (6109334864205959/100000000000000 : ℝ)*(sp1) + (3054667449989831/50000000000000 : ℝ)*(sp2) + (70523319493159/2500000000000 : ℝ)*(sp3) + (2418208873/25000000000000 : ℝ)*(sp4) + (321166669/12500000000000 : ℝ)*(sp7) + (22038557414529/781250000000 : ℝ)*(f.failure) + (6109334954948183/100000000000000 : ℝ)*(f.sum) + (19695951281139/9437500000000000000000000000 : ℝ)*base65 + (710116273468458701/47187500000000000000000000000000 : ℝ)*base67 + (461513830045958701/47187500000000000000000000000000 : ℝ)*base69 + (18293737174083701/47187500000000000000000000000000 : ℝ)*base71 + (2277972458727/294921875000000000000000000 : ℝ)*base73 + (492361264733728799/47187500000000000000000000000000 : ℝ)*base76 + (69482076643458701/47187500000000000000000000000000 : ℝ)*base77 + (860763355607833701/47187500000000000000000000000000 : ℝ)*base79 + (1787097394717/1179687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (200317/78125000000000000000 : ℝ)*base90 + (200317/78125000000000000000 : ℝ)*base92 + (200317/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90773034143394678528013269/9437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51100667/3125000000000 : ℝ)*(base19) + (1757942627/100000000000000 : ℝ)*(base23) + (202730533/100000000000000 : ℝ)*(upper3) + (63456571/100000000000000 : ℝ)*(lower4) + (183124223/100000000000000 : ℝ)*(upper5) + (449818791506327/10000000000000 : ℝ)*(major0) + (449818791506327/10000000000000 : ℝ)*(major1) + (449818791506327/10000000000000 : ℝ)*(major2) + (33755800861/100000000000000 : ℝ)*(sp1) + (36167153551/100000000000000 : ℝ)*(sp2) + (6154558472606983/100000000000000 : ℝ)*(sp4) + (6154523081584777/100000000000000 : ℝ)*(sp5) + (1230904109502161/20000000000000 : ℝ)*(sp6) + (355227129613549/12500000000000 : ℝ)*(sp7) + (355227129613549/12500000000000 : ℝ)*(f.failure) + (6154558472606983/100000000000000 : ℝ)*(f.sum) + (155178014971/117968750000000000000000000 : ℝ)*base66 + (46674852836143077/18875000000000000000000000000000 : ℝ)*base67 + (38169262044356923/18875000000000000000000000000000 : ℝ)*base70 + (194893724473768077/18875000000000000000000000000000 : ℝ)*base71 + (5750392701547/3775000000000000000000000000 : ℝ)*base74 + (99904215313231923/18875000000000000000000000000000 : ℝ)*base76 + (125137771061143077/18875000000000000000000000000000 : ℝ)*base77 + (214380027890768077/18875000000000000000000000000000 : ℝ)*base79 + (9352016925097/3775000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3839777/1250000000000000000000 : ℝ)*base90 + (3839777/1250000000000000000000 : ℝ)*base92 + (3839777/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1432_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2989/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14787/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1432_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1432_s5_0 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1968676801/10000000000 : ℝ)*x 0 + (1352060267/2500000000 : ℝ)*x 1 + (655851393/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968676801/10000000000 : ℝ)^549 ≤ (1501366207527/12500000000000 : ℝ)^421 := by
    have hnat : (1968676801 : ℕ)^549*12500000000000^421 ≤ 1501366207527^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968676801 10000000000 1501366207527 12500000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352060267/2500000000 : ℝ)^549 ≤ (5607960503177/12500000000000 : ℝ)^421 := by
    have hnat : (1352060267 : ℕ)^549*12500000000000^421 ≤ 5607960503177^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352060267 2500000000 5607960503177 12500000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655851393/1250000000 : ℝ)^549 ≤ (5390673288413/12500000000000 : ℝ)^421 := by
    have hnat : (655851393 : ℕ)^549*12500000000000^421 ≤ 5390673288413^421*1250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655851393 1250000000 5390673288413 12500000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1968676801/10000000000 : ℝ), (1352060267/2500000000 : ℝ), (655851393/1250000000 : ℝ)] ![(1501366207527/12500000000000 : ℝ), (5607960503177/12500000000000 : ℝ), (5390673288413/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1968676801/10000000000 : ℝ)|^549 ≤ (1501366207527/12500000000000 : ℝ)^421
        have hw : |(-1968676801/10000000000 : ℝ)|=(1968676801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352060267/2500000000 : ℝ)|^549 ≤ (5607960503177/12500000000000 : ℝ)^421
        have hw : |(1352060267/2500000000 : ℝ)|=(1352060267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655851393/1250000000 : ℝ)|^549 ≤ (5390673288413/12500000000000 : ℝ)^421
        have hw : |(655851393/1250000000 : ℝ)|=(655851393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s5_1 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347310301/10000000000 : ℝ)*x 0 + (-1025432103/5000000000 : ℝ)*x 1 + (655851397/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347310301/10000000000 : ℝ)^549 ≤ (44205693894943/100000000000000 : ℝ)^421 := by
    have hnat : (5347310301 : ℕ)^549*100000000000000^421 ≤ 44205693894943^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347310301 10000000000 44205693894943 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025432103/5000000000 : ℝ)^549 ≤ (6334459725571/50000000000000 : ℝ)^421 := by
    have hnat : (1025432103 : ℕ)^549*50000000000000^421 ≤ 6334459725571^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025432103 5000000000 6334459725571 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655851397/1250000000 : ℝ)^549 ≤ (43125386650291/100000000000000 : ℝ)^421 := by
    have hnat : (655851397 : ℕ)^549*100000000000000^421 ≤ 43125386650291^421*1250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655851397 1250000000 43125386650291 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347310301/10000000000 : ℝ), (-1025432103/5000000000 : ℝ), (655851397/1250000000 : ℝ)] ![(44205693894943/100000000000000 : ℝ), (6334459725571/50000000000000 : ℝ), (43125386650291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347310301/10000000000 : ℝ)|^549 ≤ (44205693894943/100000000000000 : ℝ)^421
        have hw : |(5347310301/10000000000 : ℝ)|=(5347310301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025432103/5000000000 : ℝ)|^549 ≤ (6334459725571/50000000000000 : ℝ)^421
        have hw : |(-1025432103/5000000000 : ℝ)|=(1025432103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655851397/1250000000 : ℝ)|^549 ≤ (43125386650291/100000000000000 : ℝ)^421
        have hw : |(655851397/1250000000 : ℝ)|=(655851397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s5_2 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347310261/10000000000 : ℝ)*x 0 + (327925703/625000000 : ℝ)*x 1 + (-1025432081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347310261/10000000000 : ℝ)^549 ≤ (2762855841483/6250000000000 : ℝ)^421 := by
    have hnat : (5347310261 : ℕ)^549*6250000000000^421 ≤ 2762855841483^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347310261 10000000000 2762855841483 6250000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327925703/625000000 : ℝ)^549 ≤ (10781346855503/25000000000000 : ℝ)^421 := by
    have hnat : (327925703 : ℕ)^549*25000000000000^421 ≤ 10781346855503^421*625000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327925703 625000000 10781346855503 25000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025432081/5000000000 : ℝ)^549 ≤ (12668919096699/100000000000000 : ℝ)^421 := by
    have hnat : (1025432081 : ℕ)^549*100000000000000^421 ≤ 12668919096699^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025432081 5000000000 12668919096699 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347310261/10000000000 : ℝ), (327925703/625000000 : ℝ), (-1025432081/5000000000 : ℝ)] ![(2762855841483/6250000000000 : ℝ), (10781346855503/25000000000000 : ℝ), (12668919096699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347310261/10000000000 : ℝ)|^549 ≤ (2762855841483/6250000000000 : ℝ)^421
        have hw : |(5347310261/10000000000 : ℝ)|=(5347310261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327925703/625000000 : ℝ)|^549 ≤ (10781346855503/25000000000000 : ℝ)^421
        have hw : |(327925703/625000000 : ℝ)|=(327925703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025432081/5000000000 : ℝ)|^549 ≤ (12668919096699/100000000000000 : ℝ)^421
        have hw : |(-1025432081/5000000000 : ℝ)|=(1025432081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s5_3 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2151805859/5000000000 : ℝ)*x 0 + (4131995793/10000000000 : ℝ)*x 1 + (4481606099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151805859/5000000000 : ℝ)^549 ≤ (832615383449/2500000000000 : ℝ)^421 := by
    have hnat : (2151805859 : ℕ)^549*2500000000000^421 ≤ 832615383449^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151805859 5000000000 832615383449 2500000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4131995793/10000000000 : ℝ)^549 ≤ (631666549851/2000000000000 : ℝ)^421 := by
    have hnat : (4131995793 : ℕ)^549*2000000000000^421 ≤ 631666549851^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131995793 10000000000 631666549851 2000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481606099/10000000000 : ℝ)^549 ≤ (3511205715819/10000000000000 : ℝ)^421 := by
    have hnat : (4481606099 : ℕ)^549*10000000000000^421 ≤ 3511205715819^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481606099 10000000000 3511205715819 10000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151805859/5000000000 : ℝ), (4131995793/10000000000 : ℝ), (4481606099/10000000000 : ℝ)] ![(832615383449/2500000000000 : ℝ), (631666549851/2000000000000 : ℝ), (3511205715819/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151805859/5000000000 : ℝ)|^549 ≤ (832615383449/2500000000000 : ℝ)^421
        have hw : |(2151805859/5000000000 : ℝ)|=(2151805859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4131995793/10000000000 : ℝ)|^549 ≤ (631666549851/2000000000000 : ℝ)^421
        have hw : |(4131995793/10000000000 : ℝ)|=(4131995793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481606099/10000000000 : ℝ)|^549 ≤ (3511205715819/10000000000000 : ℝ)^421
        have hw : |(4481606099/10000000000 : ℝ)|=(4481606099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s5_4 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1968688513/10000000000 : ℝ)*x 0 + (262369719/500000000 : ℝ)*x 1 + (5407654547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968688513/10000000000 : ℝ)^549 ≤ (6005511420237/50000000000000 : ℝ)^421 := by
    have hnat : (1968688513 : ℕ)^549*50000000000000^421 ≤ 6005511420237^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968688513 10000000000 6005511420237 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262369719/500000000 : ℝ)^549 ≤ (8626327547759/20000000000000 : ℝ)^421 := by
    have hnat : (262369719 : ℕ)^549*20000000000000^421 ≤ 8626327547759^421*500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262369719 500000000 8626327547759 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407654547/10000000000 : ℝ)^549 ≤ (44857339406433/100000000000000 : ℝ)^421 := by
    have hnat : (5407654547 : ℕ)^549*100000000000000^421 ≤ 44857339406433^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407654547 10000000000 44857339406433 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1968688513/10000000000 : ℝ), (262369719/500000000 : ℝ), (5407654547/10000000000 : ℝ)] ![(6005511420237/50000000000000 : ℝ), (8626327547759/20000000000000 : ℝ), (44857339406433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1968688513/10000000000 : ℝ)|^549 ≤ (6005511420237/50000000000000 : ℝ)^421
        have hw : |(-1968688513/10000000000 : ℝ)|=(1968688513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262369719/500000000 : ℝ)|^549 ≤ (8626327547759/20000000000000 : ℝ)^421
        have hw : |(262369719/500000000 : ℝ)|=(262369719/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407654547/10000000000 : ℝ)|^549 ≤ (44857339406433/100000000000000 : ℝ)^421
        have hw : |(5407654547/10000000000 : ℝ)|=(5407654547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s5_5 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (41447891/78125000 : ℝ)*x 0 + (-1890021421/10000000000 : ℝ)*x 1 + (1081530913/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41447891/78125000 : ℝ)^549 ≤ (43753672953909/100000000000000 : ℝ)^421 := by
    have hnat : (41447891 : ℕ)^549*100000000000000^421 ≤ 43753672953909^421*78125000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41447891 78125000 43753672953909 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1890021421/10000000000 : ℝ)^549 ≤ (5694493713367/50000000000000 : ℝ)^421 := by
    have hnat : (1890021421 : ℕ)^549*50000000000000^421 ≤ 5694493713367^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890021421 10000000000 5694493713367 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081530913/2000000000 : ℝ)^549 ≤ (22428669800571/50000000000000 : ℝ)^421 := by
    have hnat : (1081530913 : ℕ)^549*50000000000000^421 ≤ 22428669800571^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081530913 2000000000 22428669800571 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41447891/78125000 : ℝ), (-1890021421/10000000000 : ℝ), (1081530913/2000000000 : ℝ)] ![(43753672953909/100000000000000 : ℝ), (5694493713367/50000000000000 : ℝ), (22428669800571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41447891/78125000 : ℝ)|^549 ≤ (43753672953909/100000000000000 : ℝ)^421
        have hw : |(41447891/78125000 : ℝ)|=(41447891/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1890021421/10000000000 : ℝ)|^549 ≤ (5694493713367/50000000000000 : ℝ)^421
        have hw : |(-1890021421/10000000000 : ℝ)|=(1890021421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081530913/2000000000 : ℝ)|^549 ≤ (22428669800571/50000000000000 : ℝ)^421
        have hw : |(1081530913/2000000000 : ℝ)|=(1081530913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s5_6 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1326332637/2500000000 : ℝ)*x 0 + (2703827171/5000000000 : ℝ)*x 1 + (-472505261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326332637/2500000000 : ℝ)^549 ≤ (21876839165593/50000000000000 : ℝ)^421 := by
    have hnat : (1326332637 : ℕ)^549*50000000000000^421 ≤ 21876839165593^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326332637 2500000000 21876839165593 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703827171/5000000000 : ℝ)^549 ≤ (44857337188907/100000000000000 : ℝ)^421 := by
    have hnat : (2703827171 : ℕ)^549*100000000000000^421 ≤ 44857337188907^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703827171 5000000000 44857337188907 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472505261/2500000000 : ℝ)^549 ≤ (11388984464291/100000000000000 : ℝ)^421 := by
    have hnat : (472505261 : ℕ)^549*100000000000000^421 ≤ 11388984464291^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472505261 2500000000 11388984464291 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326332637/2500000000 : ℝ), (2703827171/5000000000 : ℝ), (-472505261/2500000000 : ℝ)] ![(21876839165593/50000000000000 : ℝ), (44857337188907/100000000000000 : ℝ), (11388984464291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326332637/2500000000 : ℝ)|^549 ≤ (21876839165593/50000000000000 : ℝ)^421
        have hw : |(1326332637/2500000000 : ℝ)|=(1326332637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703827171/5000000000 : ℝ)|^549 ≤ (44857337188907/100000000000000 : ℝ)^421
        have hw : |(2703827171/5000000000 : ℝ)|=(2703827171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-472505261/2500000000 : ℝ)|^549 ≤ (11388984464291/100000000000000 : ℝ)^421
        have hw : |(-472505261/2500000000 : ℝ)|=(472505261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s5_7 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4303636479/10000000000 : ℝ)*x 0 + (4480342109/10000000000 : ℝ)*x 1 + (4133266201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303636479/10000000000 : ℝ)^549 ≤ (1040777038037/3125000000000 : ℝ)^421 := by
    have hnat : (4303636479 : ℕ)^549*3125000000000^421 ≤ 1040777038037^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303636479 10000000000 1040777038037 3125000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480342109/10000000000 : ℝ)^549 ≤ (8774785959967/25000000000000 : ℝ)^421 := by
    have hnat : (4480342109 : ℕ)^549*25000000000000^421 ≤ 8774785959967^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480342109 10000000000 8774785959967 25000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4133266201/10000000000 : ℝ)^549 ≤ (6319198186983/20000000000000 : ℝ)^421 := by
    have hnat : (4133266201 : ℕ)^549*20000000000000^421 ≤ 6319198186983^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133266201 10000000000 6319198186983 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303636479/10000000000 : ℝ), (4480342109/10000000000 : ℝ), (4133266201/10000000000 : ℝ)] ![(1040777038037/3125000000000 : ℝ), (8774785959967/25000000000000 : ℝ), (6319198186983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303636479/10000000000 : ℝ)|^549 ≤ (1040777038037/3125000000000 : ℝ)^421
        have hw : |(4303636479/10000000000 : ℝ)|=(4303636479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480342109/10000000000 : ℝ)|^549 ≤ (8774785959967/25000000000000 : ℝ)^421
        have hw : |(4480342109/10000000000 : ℝ)|=(4480342109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4133266201/10000000000 : ℝ)|^549 ≤ (6319198186983/20000000000000 : ℝ)^421
        have hw : |(4133266201/10000000000 : ℝ)|=(4133266201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1432_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11343/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14787/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (283/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14787/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (283/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14787/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (283/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14787/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (283/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14787/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (283/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14787/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (283/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (283/2500 : ℝ) ^ (4391/1024 : ℝ) ≤ (4383108007895001/50000000000000000000 : ℝ) := by
    have hpowers : (283/2500 : ℝ)^4391 ≤ (4383108007895001/50000000000000000000 : ℝ)^1024 := by
      have hnat : (283 : ℕ)^4391*50000000000000000000^1024 ≤ 4383108007895001^1024*2500^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        283 2500 4383108007895001 50000000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (283/2500 : ℝ)) (X := (4383108007895001/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14787/100000 : ℝ) ^ (4391/1024 : ℝ) ≤ (13783021017145297/50000000000000000000 : ℝ) := by
    have hpowers : (14787/100000 : ℝ)^4391 ≤ (13783021017145297/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14787 : ℕ)^4391*50000000000000000000^1024 ≤ 13783021017145297^1024*100000^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14787 100000 13783021017145297 50000000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14787/100000 : ℝ)) (X := (13783021017145297/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004383108007895001/25000000000000000000 : ℝ) ≤ (5000204418170447/5000000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (25004383108007895001/25000000000000000000 : ℝ)^1024 ≤ (5000204418170447/5000000000000000 : ℝ)^4391 := by
      have hnat : (25004383108007895001 : ℕ)^1024*5000000000000000^4391 ≤ 5000204418170447^4391*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004383108007895001 25000000000000000000 5000204418170447 5000000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000204418170447/5000000000000000 : ℝ)) (X := (25004383108007895001/25000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009083064512520149/25000000000000000000 : ℝ) ≤ (10000847165814399/10000000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (25009083064512520149/25000000000000000000 : ℝ)^1024 ≤ (10000847165814399/10000000000000000 : ℝ)^4391 := by
      have hnat : (25009083064512520149 : ℕ)^1024*10000000000000000^4391 ≤ 10000847165814399^4391*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009083064512520149 25000000000000000000 10000847165814399 10000000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000847165814399/10000000000000000 : ℝ)) (X := (25009083064512520149/25000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013783021017145297/25000000000000000000 : ℝ) ≤ (312540171727747/312500000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (25013783021017145297/25000000000000000000 : ℝ)^1024 ≤ (312540171727747/312500000000000 : ℝ)^4391 := by
      have hnat : (25013783021017145297 : ℕ)^1024*312500000000000^4391 ≤ 312540171727747^4391*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013783021017145297 25000000000000000000 312540171727747 312500000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312540171727747/312500000000000 : ℝ)) (X := (25013783021017145297/25000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4383108007895001/50000000000000000000 : ℝ) ≤ ((17330746828156863149/17335000000000000000 : ℝ)+2*(87665894701/69340000000000 : ℝ)*(283/2500 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (17330746828156863149/17335000000000000000 : ℝ)+2*(87665894701/69340000000000 : ℝ)*(283/2500 : ℝ)=(5000204418170447/5000000000000000 : ℝ) by norm_num, show 1+2*(4383108007895001/50000000000000000000 : ℝ)=(25004383108007895001/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13783021017145297/50000000000000000000 : ℝ)+(4383108007895001/50000000000000000000 : ℝ) ≤ ((17330746828156863149/17335000000000000000 : ℝ)+(87665894701/69340000000000 : ℝ)*((14787/100000 : ℝ)+(283/2500 : ℝ)))^(4391/1024 : ℝ) := by
    rw [show (17330746828156863149/17335000000000000000 : ℝ)+(87665894701/69340000000000 : ℝ)*((14787/100000 : ℝ)+(283/2500 : ℝ))=(10000847165814399/10000000000000000 : ℝ) by norm_num, show 1+(13783021017145297/50000000000000000000 : ℝ)+(4383108007895001/50000000000000000000 : ℝ)=(25009083064512520149/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13783021017145297/50000000000000000000 : ℝ) ≤ ((17330746828156863149/17335000000000000000 : ℝ)+2*(87665894701/69340000000000 : ℝ)*(14787/100000 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (17330746828156863149/17335000000000000000 : ℝ)+2*(87665894701/69340000000000 : ℝ)*(14787/100000 : ℝ)=(312540171727747/312500000000000 : ℝ) by norm_num, show 1+2*(13783021017145297/50000000000000000000 : ℝ)=(25013783021017145297/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17330746828156863149/17335000000000000000 : ℝ)*(X 1 0+X 2 0)+(87665894701/69340000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (14787/100000 : ℝ)) (c := (17330746828156863149/17335000000000000000 : ℝ)) (alpha := (87665894701/69340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17330746828156863149/17335000000000000000 : ℝ)*(X 0 1+X 2 1)+(87665894701/69340000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (14787/100000 : ℝ)) (c := (17330746828156863149/17335000000000000000 : ℝ)) (alpha := (87665894701/69340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17330746828156863149/17335000000000000000 : ℝ)*(X 0 2+X 1 2)+(87665894701/69340000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (14787/100000 : ℝ)) (c := (17330746828156863149/17335000000000000000 : ℝ)) (alpha := (87665894701/69340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1968676801/10000000000 : ℝ)*X 0 0+(1352060267/2500000000 : ℝ)*X 0 1+(655851393/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347310301/10000000000 : ℝ)*X 1 0+(-1025432103/5000000000 : ℝ)*X 1 1+(655851397/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347310261/10000000000 : ℝ)*X 2 0+(327925703/625000000 : ℝ)*X 2 1+(-1025432081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2151805859/5000000000 : ℝ)*X 0 0+(4131995793/10000000000 : ℝ)*X 0 1+(4481606099/10000000000 : ℝ)*X 0 2+(2151805859/5000000000 : ℝ)*X 1 0+(4131995793/10000000000 : ℝ)*X 1 1+(4481606099/10000000000 : ℝ)*X 1 2+(2151805859/5000000000 : ℝ)*X 2 0+(4131995793/10000000000 : ℝ)*X 2 1+(4481606099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1968688513/10000000000 : ℝ)*X 0 0+(262369719/500000000 : ℝ)*X 0 1+(5407654547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41447891/78125000 : ℝ)*X 1 0+(-1890021421/10000000000 : ℝ)*X 1 1+(1081530913/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326332637/2500000000 : ℝ)*X 2 0+(2703827171/5000000000 : ℝ)*X 2 1+(-472505261/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4303636479/10000000000 : ℝ)*X 0 0+(4480342109/10000000000 : ℝ)*X 0 1+(4133266201/10000000000 : ℝ)*X 0 2+(4303636479/10000000000 : ℝ)*X 1 0+(4480342109/10000000000 : ℝ)*X 1 1+(4133266201/10000000000 : ℝ)*X 1 2+(4303636479/10000000000 : ℝ)*X 2 0+(4480342109/10000000000 : ℝ)*X 2 1+(4133266201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1420483363556863683838327947/433375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37118471/5000000000000 : ℝ)*(base19) + (168531889/25000000000000 : ℝ)*(base23) + (25633101/50000000000000 : ℝ)*(upper3) + (732021/6250000000000 : ℝ)*(upper4) + (10392119/12500000000000 : ℝ)*(upper5) + (2263754598959833/50000000000000 : ℝ)*(major0) + (2263754598959833/50000000000000 : ℝ)*(major1) + (2263754598959833/50000000000000 : ℝ)*(major2) + (6194656979937639/100000000000000 : ℝ)*(sp0) + (3097338110458073/50000000000000 : ℝ)*(sp1) + (6194676289158011/100000000000000 : ℝ)*(sp2) + (143016734652189/5000000000000 : ℝ)*(sp3) + (19983347927/100000000000000 : ℝ)*(sp4) + (6630252533/100000000000000 : ℝ)*(sp7) + (2860341323296313/100000000000000 : ℝ)*(f.failure) + (3097338481642783/50000000000000 : ℝ)*(f.sum) + (9404087008947/3467000000000000000000000000 : ℝ)*base65 + (2495047992766394117/866750000000000000000000000000000 : ℝ)*base67 + (4245591687625644117/866750000000000000000000000000000 : ℝ)*base69 + (16809816929054394117/866750000000000000000000000000000 : ℝ)*base71 + (13710643308121/3467000000000000000000000000 : ℝ)*base74 + (13487898956041394117/866750000000000000000000000000000 : ℝ)*base75 + (2848527824810644117/866750000000000000000000000000000 : ℝ)*base77 + (6377308770648394117/866750000000000000000000000000000 : ℝ)*base79 + (13052204427209/3467000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (9993251/10000000000000000000000 : ℝ)*base89 + (9993251/10000000000000000000000 : ℝ)*base91 + (9993251/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56951132765374095526907193/13542968750000000000000000000000 : ℝ) := by norm_num
    linear_combination (302465133/100000000000000 : ℝ)*(base19) + (1323695659/100000000000000 : ℝ)*(base23) + (179835737/100000000000000 : ℝ)*(upper2) + (14279987/100000000000000 : ℝ)*(upper3) + (423375999/100000000000000 : ℝ)*(upper5) + (570067493325851/12500000000000 : ℝ)*(major0) + (570067493325851/12500000000000 : ℝ)*(major1) + (570067493325851/12500000000000 : ℝ)*(major2) + (1055795773/12500000000000 : ℝ)*(sp1) + (20349199943/100000000000000 : ℝ)*(sp2) + (6239870616718791/100000000000000 : ℝ)*(sp4) + (249594474715499/4000000000000 : ℝ)*(sp5) + (6239848943823189/100000000000000 : ℝ)*(sp6) + (720302284080223/25000000000000 : ℝ)*(sp7) + (720302284080223/25000000000000 : ℝ)*(f.failure) + (6239870616718791/100000000000000 : ℝ)*(f.sum) + (23488626114087/3467000000000000000000000000 : ℝ)*base66 + (569829260287285201/216687500000000000000000000000000 : ℝ)*base68 + (1938344118826027299/216687500000000000000000000000000 : ℝ)*base69 + (1255340458021535201/216687500000000000000000000000000 : ℝ)*base72 + (253940878857/138680000000000000000000000 : ℝ)*base73 + (1857642345879847701/216687500000000000000000000000000 : ℝ)*base76 + (1198001155873847701/216687500000000000000000000000000 : ℝ)*base78 + (3359832703823160201/216687500000000000000000000000000 : ℝ)*base80 + (5886477991669/1733500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15854821/2500000000000000000000 : ℝ)*base89 + (15854821/2500000000000000000000 : ℝ)*base91 + (15854821/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1432_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1432_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1432_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1579/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1432_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1432_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1432_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1579/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1432_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
