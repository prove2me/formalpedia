-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1217_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:09:41.07676+00:00
-- url     : https://prove2.me/submissions/18061ea3-f5e1-4293-bb57-91a5b66ce654

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
theorem support_rectangle_w1217_s9_0 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336106337/2500000000 : ℝ)*x 0 + (5266918331/10000000000 : ℝ)*x 1 + (-2194757391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336106337/2500000000 : ℝ)^4205 ≤ (2184133943703/5000000000000 : ℝ)^3181 := by
    have hnat : (1336106337 : ℕ)^4205*5000000000000^3181 ≤ 2184133943703^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336106337 2500000000 2184133943703 5000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266918331/10000000000 : ℝ)^4205 ≤ (21423602073827/50000000000000 : ℝ)^3181 := by
    have hnat : (5266918331 : ℕ)^4205*50000000000000^3181 ≤ 21423602073827^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266918331 10000000000 21423602073827 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194757391/10000000000 : ℝ)^4205 ≤ (3367529240209/25000000000000 : ℝ)^3181 := by
    have hnat : (2194757391 : ℕ)^4205*25000000000000^3181 ≤ 3367529240209^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194757391 10000000000 3367529240209 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336106337/2500000000 : ℝ), (5266918331/10000000000 : ℝ), (-2194757391/10000000000 : ℝ)] ![(2184133943703/5000000000000 : ℝ), (21423602073827/50000000000000 : ℝ), (3367529240209/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336106337/2500000000 : ℝ)|^4205 ≤ (2184133943703/5000000000000 : ℝ)^3181
        have hw : |(1336106337/2500000000 : ℝ)|=(1336106337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266918331/10000000000 : ℝ)|^4205 ≤ (21423602073827/50000000000000 : ℝ)^3181
        have hw : |(5266918331/10000000000 : ℝ)|=(5266918331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2194757391/10000000000 : ℝ)|^4205 ≤ (3367529240209/25000000000000 : ℝ)^3181
        have hw : |(-2194757391/10000000000 : ℝ)|=(2194757391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s9_1 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065766563/5000000000 : ℝ)*x 0 + (131680817/250000000 : ℝ)*x 1 + (1347824839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065766563/5000000000 : ℝ)^4205 ≤ (12959565784069/100000000000000 : ℝ)^3181 := by
    have hnat : (1065766563 : ℕ)^4205*100000000000000^3181 ≤ 12959565784069^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065766563 5000000000 12959565784069 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131680817/250000000 : ℝ)^4205 ≤ (4285058467529/10000000000000 : ℝ)^3181 := by
    have hnat : (131680817 : ℕ)^4205*10000000000000^3181 ≤ 4285058467529^3181*250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131680817 250000000 4285058467529 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347824839/2500000000 : ℝ)^4205 ≤ (22094924762921/50000000000000 : ℝ)^3181 := by
    have hnat : (1347824839 : ℕ)^4205*50000000000000^3181 ≤ 22094924762921^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347824839 2500000000 22094924762921 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065766563/5000000000 : ℝ), (131680817/250000000 : ℝ), (1347824839/2500000000 : ℝ)] ![(12959565784069/100000000000000 : ℝ), (4285058467529/10000000000000 : ℝ), (22094924762921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065766563/5000000000 : ℝ)|^4205 ≤ (12959565784069/100000000000000 : ℝ)^3181
        have hw : |(-1065766563/5000000000 : ℝ)|=(1065766563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131680817/250000000 : ℝ)|^4205 ≤ (4285058467529/10000000000000 : ℝ)^3181
        have hw : |(131680817/250000000 : ℝ)|=(131680817/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347824839/2500000000 : ℝ)|^4205 ≤ (22094924762921/50000000000000 : ℝ)^3181
        have hw : |(1347824839/2500000000 : ℝ)|=(1347824839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s9_2 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312662503/10000000000 : ℝ)*x 0 + (-414075369/2000000000 : ℝ)*x 1 + (539129929/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312662503/10000000000 : ℝ)^4205 ≤ (43339821278093/100000000000000 : ℝ)^3181 := by
    have hnat : (5312662503 : ℕ)^4205*100000000000000^3181 ≤ 43339821278093^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312662503 10000000000 43339821278093 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414075369/2000000000 : ℝ)^4205 ≤ (6235164944947/50000000000000 : ℝ)^3181 := by
    have hnat : (414075369 : ℕ)^4205*50000000000000^3181 ≤ 6235164944947^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414075369 2000000000 6235164944947 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539129929/1000000000 : ℝ)^4205 ≤ (5523731101341/12500000000000 : ℝ)^3181 := by
    have hnat : (539129929 : ℕ)^4205*12500000000000^3181 ≤ 5523731101341^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539129929 1000000000 5523731101341 12500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312662503/10000000000 : ℝ), (-414075369/2000000000 : ℝ), (539129929/1000000000 : ℝ)] ![(43339821278093/100000000000000 : ℝ), (6235164944947/50000000000000 : ℝ), (5523731101341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312662503/10000000000 : ℝ)|^4205 ≤ (43339821278093/100000000000000 : ℝ)^3181
        have hw : |(5312662503/10000000000 : ℝ)|=(5312662503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414075369/2000000000 : ℝ)|^4205 ≤ (6235164944947/50000000000000 : ℝ)^3181
        have hw : |(-414075369/2000000000 : ℝ)|=(414075369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539129929/1000000000 : ℝ)|^4205 ≤ (5523731101341/12500000000000 : ℝ)^3181
        have hw : |(539129929/1000000000 : ℝ)|=(539129929/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s9_3 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656331349/5000000000 : ℝ)*x 0 + (1078259861/2000000000 : ℝ)*x 1 + (-2070376561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656331349/5000000000 : ℝ)^4205 ≤ (270873896131/625000000000 : ℝ)^3181 := by
    have hnat : (2656331349 : ℕ)^4205*625000000000^3181 ≤ 270873896131^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656331349 5000000000 270873896131 625000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078259861/2000000000 : ℝ)^4205 ≤ (44189848973253/100000000000000 : ℝ)^3181 := by
    have hnat : (1078259861 : ℕ)^4205*100000000000000^3181 ≤ 44189848973253^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078259861 2000000000 44189848973253 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070376561/10000000000 : ℝ)^4205 ≤ (77939547679/625000000000 : ℝ)^3181 := by
    have hnat : (2070376561 : ℕ)^4205*625000000000^3181 ≤ 77939547679^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070376561 10000000000 77939547679 625000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656331349/5000000000 : ℝ), (1078259861/2000000000 : ℝ), (-2070376561/10000000000 : ℝ)] ![(270873896131/625000000000 : ℝ), (44189848973253/100000000000000 : ℝ), (77939547679/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656331349/5000000000 : ℝ)|^4205 ≤ (270873896131/625000000000 : ℝ)^3181
        have hw : |(2656331349/5000000000 : ℝ)|=(2656331349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078259861/2000000000 : ℝ)|^4205 ≤ (44189848973253/100000000000000 : ℝ)^3181
        have hw : |(1078259861/2000000000 : ℝ)|=(1078259861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2070376561/10000000000 : ℝ)|^4205 ≤ (77939547679/625000000000 : ℝ)^3181
        have hw : |(-2070376561/10000000000 : ℝ)|=(2070376561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s9_4 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (435422533/1000000000 : ℝ)*x 0 + (140038363/312500000 : ℝ)*x 1 + (169230553/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435422533/1000000000 : ℝ)^4205 ≤ (16658742878107/50000000000000 : ℝ)^3181 := by
    have hnat : (435422533 : ℕ)^4205*50000000000000^3181 ≤ 16658742878107^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435422533 1000000000 16658742878107 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140038363/312500000 : ℝ)^4205 ≤ (4326012360761/12500000000000 : ℝ)^3181 := by
    have hnat : (140038363 : ℕ)^4205*12500000000000^3181 ≤ 4326012360761^3181*312500000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140038363 312500000 4326012360761 12500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169230553/400000000 : ℝ)^4205 ≤ (3207441533699/10000000000000 : ℝ)^3181 := by
    have hnat : (169230553 : ℕ)^4205*10000000000000^3181 ≤ 3207441533699^3181*400000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169230553 400000000 3207441533699 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435422533/1000000000 : ℝ), (140038363/312500000 : ℝ), (169230553/400000000 : ℝ)] ![(16658742878107/50000000000000 : ℝ), (4326012360761/12500000000000 : ℝ), (3207441533699/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435422533/1000000000 : ℝ)|^4205 ≤ (16658742878107/50000000000000 : ℝ)^3181
        have hw : |(435422533/1000000000 : ℝ)|=(435422533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140038363/312500000 : ℝ)|^4205 ≤ (4326012360761/12500000000000 : ℝ)^3181
        have hw : |(140038363/312500000 : ℝ)|=(140038363/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169230553/400000000 : ℝ)|^4205 ≤ (3207441533699/10000000000000 : ℝ)^3181
        have hw : |(169230553/400000000 : ℝ)|=(169230553/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1217_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11449/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1409/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14091/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14091/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14091/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14091/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14091/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14091/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11449/100000 : ℝ) ^ (8409/2048 : ℝ) ≤ (1707064924759901/12500000000000000000 : ℝ) := by
    have hpowers : (11449/100000 : ℝ)^8409 ≤ (1707064924759901/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11449 : ℕ)^8409*12500000000000000000^2048 ≤ 1707064924759901^2048*100000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11449 100000 1707064924759901 12500000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11449/100000 : ℝ)) (X := (1707064924759901/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14091/100000 : ℝ) ^ (8409/2048 : ℝ) ≤ (32032560929643153/100000000000000000000 : ℝ) := by
    have hpowers : (14091/100000 : ℝ)^8409 ≤ (32032560929643153/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14091 : ℕ)^8409*100000000000000000000^2048 ≤ 32032560929643153^2048*100000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14091 100000 32032560929643153 100000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14091/100000 : ℝ)) (X := (32032560929643153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251707064924759901/6250000000000000000 : ℝ) ≤ (2500166284117611/2500000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (6251707064924759901/6250000000000000000 : ℝ)^2048 ≤ (2500166284117611/2500000000000000 : ℝ)^8409 := by
      have hnat : (6251707064924759901 : ℕ)^2048*2500000000000000^8409 ≤ 2500166284117611^8409*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251707064924759901 6250000000000000000 2500166284117611 2500000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500166284117611/2500000000000000 : ℝ)) (X := (6251707064924759901/6250000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045689080327722361/100000000000000000000 : ℝ) ≤ (10001112558817829/10000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (100045689080327722361/100000000000000000000 : ℝ)^2048 ≤ (10001112558817829/10000000000000000 : ℝ)^8409 := by
      have hnat : (100045689080327722361 : ℕ)^2048*10000000000000000^8409 ≤ 10001112558817829^8409*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045689080327722361 100000000000000000000 10001112558817829 10000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001112558817829/10000000000000000 : ℝ)) (X := (100045689080327722361/100000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032032560929643153/50000000000000000000 : ℝ) ≤ (5000779990582607/5000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (50032032560929643153/50000000000000000000 : ℝ)^2048 ≤ (5000779990582607/5000000000000000 : ℝ)^8409 := by
      have hnat : (50032032560929643153 : ℕ)^2048*5000000000000000^8409 ≤ 5000779990582607^8409*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032032560929643153 50000000000000000000 5000779990582607 5000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000779990582607/5000000000000000 : ℝ)) (X := (50032032560929643153/50000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1707064924759901/12500000000000000000 : ℝ) ≤ ((13205756106822245659/13210000000000000000 : ℝ)+2*(89484469477/52840000000000 : ℝ)*(11449/100000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (13205756106822245659/13210000000000000000 : ℝ)+2*(89484469477/52840000000000 : ℝ)*(11449/100000 : ℝ)=(2500166284117611/2500000000000000 : ℝ) by norm_num, show 1+2*(1707064924759901/12500000000000000000 : ℝ)=(6251707064924759901/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32032560929643153/100000000000000000000 : ℝ)+(1707064924759901/12500000000000000000 : ℝ) ≤ ((13205756106822245659/13210000000000000000 : ℝ)+(89484469477/52840000000000 : ℝ)*((14091/100000 : ℝ)+(11449/100000 : ℝ)))^(8409/2048 : ℝ) := by
    rw [show (13205756106822245659/13210000000000000000 : ℝ)+(89484469477/52840000000000 : ℝ)*((14091/100000 : ℝ)+(11449/100000 : ℝ))=(10001112558817829/10000000000000000 : ℝ) by norm_num, show 1+(32032560929643153/100000000000000000000 : ℝ)+(1707064924759901/12500000000000000000 : ℝ)=(100045689080327722361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32032560929643153/100000000000000000000 : ℝ) ≤ ((13205756106822245659/13210000000000000000 : ℝ)+2*(89484469477/52840000000000 : ℝ)*(14091/100000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (13205756106822245659/13210000000000000000 : ℝ)+2*(89484469477/52840000000000 : ℝ)*(14091/100000 : ℝ)=(5000779990582607/5000000000000000 : ℝ) by norm_num, show 1+2*(32032560929643153/100000000000000000000 : ℝ)=(50032032560929643153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13205756106822245659/13210000000000000000 : ℝ)*(X 1 0+X 2 0)+(89484469477/52840000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (13205756106822245659/13210000000000000000 : ℝ)) (alpha := (89484469477/52840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13205756106822245659/13210000000000000000 : ℝ)*(X 0 1+X 2 1)+(89484469477/52840000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (13205756106822245659/13210000000000000000 : ℝ)) (alpha := (89484469477/52840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13205756106822245659/13210000000000000000 : ℝ)*(X 0 2+X 1 2)+(89484469477/52840000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (13205756106822245659/13210000000000000000 : ℝ)) (alpha := (89484469477/52840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1336106337/2500000000 : ℝ)*X 2 0+(5266918331/10000000000 : ℝ)*X 2 1+(-2194757391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1065766563/5000000000 : ℝ)*X 0 0+(131680817/250000000 : ℝ)*X 0 1+(1347824839/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312662503/10000000000 : ℝ)*X 1 0+(-414075369/2000000000 : ℝ)*X 1 1+(539129929/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656331349/5000000000 : ℝ)*X 2 0+(1078259861/2000000000 : ℝ)*X 2 1+(-2070376561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((435422533/1000000000 : ℝ)*X 0 0+(140038363/312500000 : ℝ)*X 0 1+(169230553/400000000 : ℝ)*X 0 2+(435422533/1000000000 : ℝ)*X 1 0+(140038363/312500000 : ℝ)*X 1 1+(169230553/400000000 : ℝ)*X 1 2+(435422533/1000000000 : ℝ)*X 2 0+(140038363/312500000 : ℝ)*X 2 1+(169230553/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22588416851305708797927363/41281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (359425973/50000000000000 : ℝ)*(base19) + (1197495743/100000000000000 : ℝ)*(base23) + (93413761/50000000000000 : ℝ)*(lower1) + (22818179/25000000000000 : ℝ)*(upper3) + (21076159/100000000000000 : ℝ)*(lower4) + (23959473/50000000000000 : ℝ)*(upper5) + (753297335376331/12500000000000 : ℝ)*(major0) + (753297335376331/12500000000000 : ℝ)*(major1) + (753297335376331/12500000000000 : ℝ)*(major2) + (23939394343/100000000000000 : ℝ)*(sp0) + (8060168783467631/100000000000000 : ℝ)*(sp1) + (1612033612923137/20000000000000 : ℝ)*(sp2) + (1612028729315509/20000000000000 : ℝ)*(sp3) + (3992588564314193/100000000000000 : ℝ)*(sp4) + (3992588564314193/100000000000000 : ℝ)*(f.failure) + (8060168783467631/100000000000000 : ℝ)*(f.sum) + (1134449102121/330250000000000000000000000 : ℝ)*base65 + (2935520941926847129/165125000000000000000000000000000 : ℝ)*base67 + (2211616427220222129/165125000000000000000000000000000 : ℝ)*base69 + (11034043040437777871/165125000000000000000000000000000 : ℝ)*base72 + (299896257107/52840000000000000000000000 : ℝ)*base74 + (9773314677658472129/165125000000000000000000000000000 : ℝ)*base75 + (2113578808024847129/165125000000000000000000000000000 : ℝ)*base77 + (2531604274222097129/165125000000000000000000000000000 : ℝ)*base79 + (4980539884741/1321000000000000000000000000 : ℝ)*base81 + (148521/19531250000000000000 : ℝ)*base90 + (148521/19531250000000000000 : ℝ)*base92 + (148521/19531250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1217_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1217_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1217_box_0 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2007061653/10000000000 : ℝ)*x 0 + (2687606999/5000000000 : ℝ)*x 1 + (5375214191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2007061653/10000000000 : ℝ)^4205 ≤ (2992175762409/25000000000000 : ℝ)^3181 := by
    have hnat : (2007061653 : ℕ)^4205*25000000000000^3181 ≤ 2992175762409^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007061653 10000000000 2992175762409 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687606999/5000000000 : ℝ)^4205 ≤ (22007823712471/50000000000000 : ℝ)^3181 := by
    have hnat : (2687606999 : ℕ)^4205*50000000000000^3181 ≤ 22007823712471^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687606999 5000000000 22007823712471 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375214191/10000000000 : ℝ)^4205 ≤ (22007824757049/50000000000000 : ℝ)^3181 := by
    have hnat : (5375214191 : ℕ)^4205*50000000000000^3181 ≤ 22007824757049^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375214191 10000000000 22007824757049 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2007061653/10000000000 : ℝ), (2687606999/5000000000 : ℝ), (5375214191/10000000000 : ℝ)] ![(2992175762409/25000000000000 : ℝ), (22007823712471/50000000000000 : ℝ), (22007824757049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2007061653/10000000000 : ℝ)|^4205 ≤ (2992175762409/25000000000000 : ℝ)^3181
        have hw : |(-2007061653/10000000000 : ℝ)|=(2007061653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687606999/5000000000 : ℝ)|^4205 ≤ (22007823712471/50000000000000 : ℝ)^3181
        have hw : |(2687606999/5000000000 : ℝ)|=(2687606999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375214191/10000000000 : ℝ)|^4205 ≤ (22007824757049/50000000000000 : ℝ)^3181
        have hw : |(5375214191/10000000000 : ℝ)|=(5375214191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_1 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296615793/10000000000 : ℝ)*x 0 + (-528458081/2500000000 : ℝ)*x 1 + (1343803523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296615793/10000000000 : ℝ)^4205 ≤ (43166858803181/100000000000000 : ℝ)^3181 := by
    have hnat : (5296615793 : ℕ)^4205*100000000000000^3181 ≤ 43166858803181^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296615793 10000000000 43166858803181 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528458081/2500000000 : ℝ)^4205 ≤ (12817492744981/100000000000000 : ℝ)^3181 := by
    have hnat : (528458081 : ℕ)^4205*100000000000000^3181 ≤ 12817492744981^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528458081 2500000000 12817492744981 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343803523/2500000000 : ℝ)^4205 ≤ (22007824221229/50000000000000 : ℝ)^3181 := by
    have hnat : (1343803523 : ℕ)^4205*50000000000000^3181 ≤ 22007824221229^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343803523 2500000000 22007824221229 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296615793/10000000000 : ℝ), (-528458081/2500000000 : ℝ), (1343803523/2500000000 : ℝ)] ![(43166858803181/100000000000000 : ℝ), (12817492744981/100000000000000 : ℝ), (22007824221229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296615793/10000000000 : ℝ)|^4205 ≤ (43166858803181/100000000000000 : ℝ)^3181
        have hw : |(5296615793/10000000000 : ℝ)|=(5296615793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528458081/2500000000 : ℝ)|^4205 ≤ (12817492744981/100000000000000 : ℝ)^3181
        have hw : |(-528458081/2500000000 : ℝ)|=(528458081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343803523/2500000000 : ℝ)|^4205 ≤ (22007824221229/50000000000000 : ℝ)^3181
        have hw : |(1343803523/2500000000 : ℝ)|=(1343803523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_2 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296615813/10000000000 : ℝ)*x 0 + (2687607023/5000000000 : ℝ)*x 1 + (-52845809/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296615813/10000000000 : ℝ)^4205 ≤ (863337180373/2000000000000 : ℝ)^3181 := by
    have hnat : (5296615813 : ℕ)^4205*2000000000000^3181 ≤ 863337180373^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296615813 10000000000 863337180373 2000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687607023/5000000000 : ℝ)^4205 ≤ (1760625917781/4000000000000 : ℝ)^3181 := by
    have hnat : (2687607023 : ℕ)^4205*4000000000000^3181 ≤ 1760625917781^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687607023 5000000000 1760625917781 4000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52845809/250000000 : ℝ)^4205 ≤ (12817493033541/100000000000000 : ℝ)^3181 := by
    have hnat : (52845809 : ℕ)^4205*100000000000000^3181 ≤ 12817493033541^3181*250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52845809 250000000 12817493033541 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296615813/10000000000 : ℝ), (2687607023/5000000000 : ℝ), (-52845809/250000000 : ℝ)] ![(863337180373/2000000000000 : ℝ), (1760625917781/4000000000000 : ℝ), (12817493033541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296615813/10000000000 : ℝ)|^4205 ≤ (863337180373/2000000000000 : ℝ)^3181
        have hw : |(5296615813/10000000000 : ℝ)|=(5296615813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687607023/5000000000 : ℝ)|^4205 ≤ (1760625917781/4000000000000 : ℝ)^3181
        have hw : |(2687607023/5000000000 : ℝ)|=(2687607023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52845809/250000000 : ℝ)|^4205 ≤ (12817493033541/100000000000000 : ℝ)^3181
        have hw : |(-52845809/250000000 : ℝ)|=(52845809/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_3 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4460982497/10000000000 : ℝ)*x 0 + (860577943/2000000000 : ℝ)*x 1 + (4302889679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460982497/10000000000 : ℝ)^4205 ≤ (17200783487257/50000000000000 : ℝ)^3181 := by
    have hnat : (4460982497 : ℕ)^4205*50000000000000^3181 ≤ 17200783487257^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460982497 10000000000 17200783487257 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (860577943/2000000000 : ℝ)^4205 ≤ (32799216685727/100000000000000 : ℝ)^3181 := by
    have hnat : (860577943 : ℕ)^4205*100000000000000^3181 ≤ 32799216685727^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860577943 2000000000 32799216685727 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4302889679/10000000000 : ℝ)^4205 ≤ (32799216322977/100000000000000 : ℝ)^3181 := by
    have hnat : (4302889679 : ℕ)^4205*100000000000000^3181 ≤ 32799216322977^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302889679 10000000000 32799216322977 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460982497/10000000000 : ℝ), (860577943/2000000000 : ℝ), (4302889679/10000000000 : ℝ)] ![(17200783487257/50000000000000 : ℝ), (32799216685727/100000000000000 : ℝ), (32799216322977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460982497/10000000000 : ℝ)|^4205 ≤ (17200783487257/50000000000000 : ℝ)^3181
        have hw : |(4460982497/10000000000 : ℝ)|=(4460982497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(860577943/2000000000 : ℝ)|^4205 ≤ (32799216685727/100000000000000 : ℝ)^3181
        have hw : |(860577943/2000000000 : ℝ)|=(860577943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4302889679/10000000000 : ℝ)|^4205 ≤ (32799216322977/100000000000000 : ℝ)^3181
        have hw : |(4302889679/10000000000 : ℝ)|=(4302889679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_4 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-225738231/1000000000 : ℝ)*x 0 + (2641012731/5000000000 : ℝ)*x 1 + (5282025533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225738231/1000000000 : ℝ)^4205 ≤ (13980518191731/100000000000000 : ℝ)^3181 := by
    have hnat : (225738231 : ℕ)^4205*100000000000000^3181 ≤ 13980518191731^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225738231 1000000000 13980518191731 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641012731/5000000000 : ℝ)^4205 ≤ (43009740517353/100000000000000 : ℝ)^3181 := by
    have hnat : (2641012731 : ℕ)^4205*100000000000000^3181 ≤ 43009740517353^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641012731 5000000000 43009740517353 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282025533/10000000000 : ℝ)^4205 ≤ (10752435320397/25000000000000 : ℝ)^3181 := by
    have hnat : (5282025533 : ℕ)^4205*25000000000000^3181 ≤ 10752435320397^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282025533 10000000000 10752435320397 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-225738231/1000000000 : ℝ), (2641012731/5000000000 : ℝ), (5282025533/10000000000 : ℝ)] ![(13980518191731/100000000000000 : ℝ), (43009740517353/100000000000000 : ℝ), (10752435320397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-225738231/1000000000 : ℝ)|^4205 ≤ (13980518191731/100000000000000 : ℝ)^3181
        have hw : |(-225738231/1000000000 : ℝ)|=(225738231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641012731/5000000000 : ℝ)|^4205 ≤ (43009740517353/100000000000000 : ℝ)^3181
        have hw : |(2641012731/5000000000 : ℝ)|=(2641012731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282025533/10000000000 : ℝ)|^4205 ≤ (10752435320397/25000000000000 : ℝ)^3181
        have hw : |(5282025533/10000000000 : ℝ)|=(5282025533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_5 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362343783/10000000000 : ℝ)*x 0 + (-215070511/1000000000 : ℝ)*x 1 + (2641012629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362343783/10000000000 : ℝ)^4205 ≤ (10969096408657/25000000000000 : ℝ)^3181 := by
    have hnat : (5362343783 : ℕ)^4205*25000000000000^3181 ≤ 10969096408657^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362343783 10000000000 10969096408657 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215070511/1000000000 : ℝ)^4205 ≤ (104911008227/800000000000 : ℝ)^3181 := by
    have hnat : (215070511 : ℕ)^4205*800000000000^3181 ≤ 104911008227^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215070511 1000000000 104911008227 800000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641012629/5000000000 : ℝ)^4205 ≤ (21504869160761/50000000000000 : ℝ)^3181 := by
    have hnat : (2641012629 : ℕ)^4205*50000000000000^3181 ≤ 21504869160761^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641012629 5000000000 21504869160761 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362343783/10000000000 : ℝ), (-215070511/1000000000 : ℝ), (2641012629/5000000000 : ℝ)] ![(10969096408657/25000000000000 : ℝ), (104911008227/800000000000 : ℝ), (21504869160761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362343783/10000000000 : ℝ)|^4205 ≤ (10969096408657/25000000000000 : ℝ)^3181
        have hw : |(5362343783/10000000000 : ℝ)|=(5362343783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215070511/1000000000 : ℝ)|^4205 ≤ (104911008227/800000000000 : ℝ)^3181
        have hw : |(-215070511/1000000000 : ℝ)|=(215070511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641012629/5000000000 : ℝ)|^4205 ≤ (21504869160761/50000000000000 : ℝ)^3181
        have hw : |(2641012629/5000000000 : ℝ)|=(2641012629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_6 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536234319/1000000000 : ℝ)*x 0 + (5282025711/10000000000 : ℝ)*x 1 + (-2150705301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536234319/1000000000 : ℝ)^4205 ≤ (8775275844113/20000000000000 : ℝ)^3181 := by
    have hnat : (536234319 : ℕ)^4205*20000000000000^3181 ≤ 8775275844113^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536234319 1000000000 8775275844113 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282025711/10000000000 : ℝ)^4205 ≤ (21504871598779/50000000000000 : ℝ)^3181 := by
    have hnat : (5282025711 : ℕ)^4205*50000000000000^3181 ≤ 21504871598779^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282025711 10000000000 21504871598779 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150705301/10000000000 : ℝ)^4205 ≤ (13113877567897/100000000000000 : ℝ)^3181 := by
    have hnat : (2150705301 : ℕ)^4205*100000000000000^3181 ≤ 13113877567897^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150705301 10000000000 13113877567897 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536234319/1000000000 : ℝ), (5282025711/10000000000 : ℝ), (-2150705301/10000000000 : ℝ)] ![(8775275844113/20000000000000 : ℝ), (21504871598779/50000000000000 : ℝ), (13113877567897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536234319/1000000000 : ℝ)|^4205 ≤ (8775275844113/20000000000000 : ℝ)^3181
        have hw : |(536234319/1000000000 : ℝ)|=(536234319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282025711/10000000000 : ℝ)|^4205 ≤ (21504871598779/50000000000000 : ℝ)^3181
        have hw : |(5282025711/10000000000 : ℝ)|=(5282025711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2150705301/10000000000 : ℝ)|^4205 ≤ (13113877567897/100000000000000 : ℝ)^3181
        have hw : |(-2150705301/10000000000 : ℝ)|=(2150705301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_7 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061764029/2500000000 : ℝ)*x 0 + (4409832661/10000000000 : ℝ)*x 1 + (4409832563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061764029/2500000000 : ℝ)^4205 ≤ (32237793243077/100000000000000 : ℝ)^3181 := by
    have hnat : (1061764029 : ℕ)^4205*100000000000000^3181 ≤ 32237793243077^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061764029 2500000000 32237793243077 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4409832661/10000000000 : ℝ)^4205 ≤ (33881103868531/100000000000000 : ℝ)^3181 := by
    have hnat : (4409832661 : ℕ)^4205*100000000000000^3181 ≤ 33881103868531^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4409832661 10000000000 33881103868531 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4409832563/10000000000 : ℝ)^4205 ≤ (4235137859151/12500000000000 : ℝ)^3181 := by
    have hnat : (4409832563 : ℕ)^4205*12500000000000^3181 ≤ 4235137859151^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4409832563 10000000000 4235137859151 12500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061764029/2500000000 : ℝ), (4409832661/10000000000 : ℝ), (4409832563/10000000000 : ℝ)] ![(32237793243077/100000000000000 : ℝ), (33881103868531/100000000000000 : ℝ), (4235137859151/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061764029/2500000000 : ℝ)|^4205 ≤ (32237793243077/100000000000000 : ℝ)^3181
        have hw : |(1061764029/2500000000 : ℝ)|=(1061764029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4409832661/10000000000 : ℝ)|^4205 ≤ (33881103868531/100000000000000 : ℝ)^3181
        have hw : |(4409832661/10000000000 : ℝ)|=(4409832661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4409832563/10000000000 : ℝ)|^4205 ≤ (4235137859151/12500000000000 : ℝ)^3181
        have hw : |(4409832563/10000000000 : ℝ)|=(4409832563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_8 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2204954207/10000000000 : ℝ)*x 0 + (1304626859/2500000000 : ℝ)*x 1 + (26924131/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2204954207/10000000000 : ℝ)^4205 ≤ (2710581322801/20000000000000 : ℝ)^3181 := by
    have hnat : (2204954207 : ℕ)^4205*20000000000000^3181 ≤ 2710581322801^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204954207 10000000000 2710581322801 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304626859/2500000000 : ℝ)^4205 ≤ (4232736734399/10000000000000 : ℝ)^3181 := by
    have hnat : (1304626859 : ℕ)^4205*10000000000000^3181 ≤ 4232736734399^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304626859 2500000000 4232736734399 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26924131/50000000 : ℝ)^4205 ≤ (11029931509061/25000000000000 : ℝ)^3181 := by
    have hnat : (26924131 : ℕ)^4205*25000000000000^3181 ≤ 11029931509061^3181*50000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26924131 50000000 11029931509061 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2204954207/10000000000 : ℝ), (1304626859/2500000000 : ℝ), (26924131/50000000 : ℝ)] ![(2710581322801/20000000000000 : ℝ), (4232736734399/10000000000000 : ℝ), (11029931509061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2204954207/10000000000 : ℝ)|^4205 ≤ (2710581322801/20000000000000 : ℝ)^3181
        have hw : |(-2204954207/10000000000 : ℝ)|=(2204954207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304626859/2500000000 : ℝ)|^4205 ≤ (4232736734399/10000000000000 : ℝ)^3181
        have hw : |(1304626859/2500000000 : ℝ)|=(1304626859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26924131/50000000 : ℝ)|^4205 ≤ (11029931509061/25000000000000 : ℝ)^3181
        have hw : |(26924131/50000000 : ℝ)|=(26924131/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_9 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661229149/1250000000 : ℝ)*x 0 + (-527490321/2500000000 : ℝ)*x 1 + (5384826083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661229149/1250000000 : ℝ)^4205 ≤ (43093801938909/100000000000000 : ℝ)^3181 := by
    have hnat : (661229149 : ℕ)^4205*100000000000000^3181 ≤ 43093801938909^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661229149 1250000000 43093801938909 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527490321/2500000000 : ℝ)^4205 ≤ (12786473269311/100000000000000 : ℝ)^3181 := by
    have hnat : (527490321 : ℕ)^4205*100000000000000^3181 ≤ 12786473269311^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527490321 2500000000 12786473269311 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384826083/10000000000 : ℝ)^4205 ≤ (5514965596129/12500000000000 : ℝ)^3181 := by
    have hnat : (5384826083 : ℕ)^4205*12500000000000^3181 ≤ 5514965596129^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384826083 10000000000 5514965596129 12500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661229149/1250000000 : ℝ), (-527490321/2500000000 : ℝ), (5384826083/10000000000 : ℝ)] ![(43093801938909/100000000000000 : ℝ), (12786473269311/100000000000000 : ℝ), (5514965596129/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661229149/1250000000 : ℝ)|^4205 ≤ (43093801938909/100000000000000 : ℝ)^3181
        have hw : |(661229149/1250000000 : ℝ)|=(661229149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-527490321/2500000000 : ℝ)|^4205 ≤ (12786473269311/100000000000000 : ℝ)^3181
        have hw : |(-527490321/2500000000 : ℝ)|=(527490321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384826083/10000000000 : ℝ)|^4205 ≤ (5514965596129/12500000000000 : ℝ)^3181
        have hw : |(5384826083/10000000000 : ℝ)|=(5384826083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_10 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322458287/2500000000 : ℝ)*x 0 + (1346206573/2500000000 : ℝ)*x 1 + (-1054980531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322458287/2500000000 : ℝ)^4205 ≤ (43093801465073/100000000000000 : ℝ)^3181 := by
    have hnat : (1322458287 : ℕ)^4205*100000000000000^3181 ≤ 43093801465073^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322458287 2500000000 43093801465073 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346206573/2500000000 : ℝ)^4205 ≤ (8823945406537/20000000000000 : ℝ)^3181 := by
    have hnat : (1346206573 : ℕ)^4205*20000000000000^3181 ≤ 8823945406537^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346206573 2500000000 8823945406537 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054980531/5000000000 : ℝ)^4205 ≤ (6393235745451/50000000000000 : ℝ)^3181 := by
    have hnat : (1054980531 : ℕ)^4205*50000000000000^3181 ≤ 6393235745451^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054980531 5000000000 6393235745451 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322458287/2500000000 : ℝ), (1346206573/2500000000 : ℝ), (-1054980531/5000000000 : ℝ)] ![(43093801465073/100000000000000 : ℝ), (8823945406537/20000000000000 : ℝ), (6393235745451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322458287/2500000000 : ℝ)|^4205 ≤ (43093801465073/100000000000000 : ℝ)^3181
        have hw : |(1322458287/2500000000 : ℝ)|=(1322458287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346206573/2500000000 : ℝ)|^4205 ≤ (8823945406537/20000000000000 : ℝ)^3181
        have hw : |(1346206573/2500000000 : ℝ)|=(1346206573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054980531/5000000000 : ℝ)|^4205 ≤ (6393235745451/50000000000000 : ℝ)^3181
        have hw : |(-1054980531/5000000000 : ℝ)|=(1054980531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_11 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2241387789/5000000000 : ℝ)*x 0 + (4291852563/10000000000 : ℝ)*x 1 + (2145926353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2241387789/5000000000 : ℝ)^4205 ≤ (6924780580773/20000000000000 : ℝ)^3181 := by
    have hnat : (2241387789 : ℕ)^4205*20000000000000^3181 ≤ 6924780580773^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241387789 5000000000 6924780580773 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4291852563/10000000000 : ℝ)^4205 ≤ (32688047821817/100000000000000 : ℝ)^3181 := by
    have hnat : (4291852563 : ℕ)^4205*100000000000000^3181 ≤ 32688047821817^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291852563 10000000000 32688047821817 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145926353/5000000000 : ℝ)^4205 ≤ (2043003078847/6250000000000 : ℝ)^3181 := by
    have hnat : (2145926353 : ℕ)^4205*6250000000000^3181 ≤ 2043003078847^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145926353 5000000000 2043003078847 6250000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2241387789/5000000000 : ℝ), (4291852563/10000000000 : ℝ), (2145926353/5000000000 : ℝ)] ![(6924780580773/20000000000000 : ℝ), (32688047821817/100000000000000 : ℝ), (2043003078847/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2241387789/5000000000 : ℝ)|^4205 ≤ (6924780580773/20000000000000 : ℝ)^3181
        have hw : |(2241387789/5000000000 : ℝ)|=(2241387789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4291852563/10000000000 : ℝ)|^4205 ≤ (32688047821817/100000000000000 : ℝ)^3181
        have hw : |(4291852563/10000000000 : ℝ)|=(4291852563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2145926353/5000000000 : ℝ)|^4205 ≤ (2043003078847/6250000000000 : ℝ)^3181
        have hw : |(2145926353/5000000000 : ℝ)|=(2145926353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_12 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2059764197/10000000000 : ℝ)*x 0 + (1359376773/2500000000 : ℝ)*x 1 + (41202777/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059764197/10000000000 : ℝ)^4205 ≤ (12385900091521/100000000000000 : ℝ)^3181 := by
    have hnat : (2059764197 : ℕ)^4205*100000000000000^3181 ≤ 12385900091521^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059764197 10000000000 12385900091521 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359376773/2500000000 : ℝ)^4205 ≤ (44691202558747/100000000000000 : ℝ)^3181 := by
    have hnat : (1359376773 : ℕ)^4205*100000000000000^3181 ≤ 44691202558747^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359376773 2500000000 44691202558747 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41202777/78125000 : ℝ)^4205 ≤ (42922897346459/100000000000000 : ℝ)^3181 := by
    have hnat : (41202777 : ℕ)^4205*100000000000000^3181 ≤ 42922897346459^3181*78125000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41202777 78125000 42922897346459 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2059764197/10000000000 : ℝ), (1359376773/2500000000 : ℝ), (41202777/78125000 : ℝ)] ![(12385900091521/100000000000000 : ℝ), (44691202558747/100000000000000 : ℝ), (42922897346459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2059764197/10000000000 : ℝ)|^4205 ≤ (12385900091521/100000000000000 : ℝ)^3181
        have hw : |(-2059764197/10000000000 : ℝ)|=(2059764197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359376773/2500000000 : ℝ)|^4205 ≤ (44691202558747/100000000000000 : ℝ)^3181
        have hw : |(1359376773/2500000000 : ℝ)|=(1359376773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41202777/78125000 : ℝ)|^4205 ≤ (42922897346459/100000000000000 : ℝ)^3181
        have hw : |(41202777/78125000 : ℝ)|=(41202777/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_13 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684016749/5000000000 : ℝ)*x 0 + (-2153841673/10000000000 : ℝ)*x 1 + (2636977783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684016749/5000000000 : ℝ)^4205 ≤ (4393793777807/10000000000000 : ℝ)^3181 := by
    have hnat : (2684016749 : ℕ)^4205*10000000000000^3181 ≤ 4393793777807^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684016749 5000000000 4393793777807 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2153841673/10000000000 : ℝ)^4205 ≤ (2627832735441/20000000000000 : ℝ)^3181 := by
    have hnat : (2153841673 : ℕ)^4205*20000000000000^3181 ≤ 2627832735441^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153841673 10000000000 2627832735441 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636977783/5000000000 : ℝ)^4205 ≤ (42922898529903/100000000000000 : ℝ)^3181 := by
    have hnat : (2636977783 : ℕ)^4205*100000000000000^3181 ≤ 42922898529903^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636977783 5000000000 42922898529903 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684016749/5000000000 : ℝ), (-2153841673/10000000000 : ℝ), (2636977783/5000000000 : ℝ)] ![(4393793777807/10000000000000 : ℝ), (2627832735441/20000000000000 : ℝ), (42922898529903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684016749/5000000000 : ℝ)|^4205 ≤ (4393793777807/10000000000000 : ℝ)^3181
        have hw : |(2684016749/5000000000 : ℝ)|=(2684016749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2153841673/10000000000 : ℝ)|^4205 ≤ (2627832735441/20000000000000 : ℝ)^3181
        have hw : |(-2153841673/10000000000 : ℝ)|=(2153841673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636977783/5000000000 : ℝ)|^4205 ≤ (42922898529903/100000000000000 : ℝ)^3181
        have hw : |(2636977783/5000000000 : ℝ)|=(2636977783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_14 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342008361/2500000000 : ℝ)*x 0 + (20601389/39062500 : ℝ)*x 1 + (-2153841721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342008361/2500000000 : ℝ)^4205 ≤ (43937937193791/100000000000000 : ℝ)^3181 := by
    have hnat : (1342008361 : ℕ)^4205*100000000000000^3181 ≤ 43937937193791^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342008361 2500000000 43937937193791 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20601389/39062500 : ℝ)^4205 ≤ (42922898723557/100000000000000 : ℝ)^3181 := by
    have hnat : (20601389 : ℕ)^4205*100000000000000^3181 ≤ 42922898723557^3181*39062500^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20601389 39062500 42922898723557 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153841721/10000000000 : ℝ)^4205 ≤ (6569582032141/50000000000000 : ℝ)^3181 := by
    have hnat : (2153841721 : ℕ)^4205*50000000000000^3181 ≤ 6569582032141^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153841721 10000000000 6569582032141 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342008361/2500000000 : ℝ), (20601389/39062500 : ℝ), (-2153841721/10000000000 : ℝ)] ![(43937937193791/100000000000000 : ℝ), (42922898723557/100000000000000 : ℝ), (6569582032141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342008361/2500000000 : ℝ)|^4205 ≤ (43937937193791/100000000000000 : ℝ)^3181
        have hw : |(1342008361/2500000000 : ℝ)|=(1342008361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20601389/39062500 : ℝ)|^4205 ≤ (42922898723557/100000000000000 : ℝ)^3181
        have hw : |(20601389/39062500 : ℝ)|=(20601389/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153841721/10000000000 : ℝ)|^4205 ≤ (6569582032141/50000000000000 : ℝ)^3181
        have hw : |(-2153841721/10000000000 : ℝ)|=(2153841721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_box_15 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2114149849/5000000000 : ℝ)*x 0 + (4419088203/10000000000 : ℝ)*x 1 + (2209544141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114149849/5000000000 : ℝ)^4205 ≤ (16024861429811/50000000000000 : ℝ)^3181 := by
    have hnat : (2114149849 : ℕ)^4205*50000000000000^3181 ≤ 16024861429811^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114149849 5000000000 16024861429811 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4419088203/10000000000 : ℝ)^4205 ≤ (33975138158147/100000000000000 : ℝ)^3181 := by
    have hnat : (4419088203 : ℕ)^4205*100000000000000^3181 ≤ 33975138158147^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419088203 10000000000 33975138158147 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209544141/5000000000 : ℝ)^4205 ≤ (424689237013/1250000000000 : ℝ)^3181 := by
    have hnat : (2209544141 : ℕ)^4205*1250000000000^3181 ≤ 424689237013^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209544141 5000000000 424689237013 1250000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114149849/5000000000 : ℝ), (4419088203/10000000000 : ℝ), (2209544141/5000000000 : ℝ)] ![(16024861429811/50000000000000 : ℝ), (33975138158147/100000000000000 : ℝ), (424689237013/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114149849/5000000000 : ℝ)|^4205 ≤ (16024861429811/50000000000000 : ℝ)^3181
        have hw : |(2114149849/5000000000 : ℝ)|=(2114149849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4419088203/10000000000 : ℝ)|^4205 ≤ (33975138158147/100000000000000 : ℝ)^3181
        have hw : |(4419088203/10000000000 : ℝ)|=(4419088203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209544141/5000000000 : ℝ)|^4205 ≤ (424689237013/1250000000000 : ℝ)^3181
        have hw : |(2209544141/5000000000 : ℝ)|=(2209544141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1217_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31121/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59357/100000 : ℝ) ∧ (16007/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83291/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11449/100000 : ℝ) ^ (8409/2048 : ℝ) ≤ (1707064924759901/12500000000000000000 : ℝ) := by
    have hpowers : (11449/100000 : ℝ)^8409 ≤ (1707064924759901/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11449 : ℕ)^8409*12500000000000000000^2048 ≤ 1707064924759901^2048*100000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11449 100000 1707064924759901 12500000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11449/100000 : ℝ)) (X := (1707064924759901/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1409/10000 : ℝ) ^ (8409/2048 : ℝ) ≤ (32023228034595451/100000000000000000000 : ℝ) := by
    have hpowers : (1409/10000 : ℝ)^8409 ≤ (32023228034595451/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1409 : ℕ)^8409*100000000000000000000^2048 ≤ 32023228034595451^2048*10000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 10000 32023228034595451 100000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/10000 : ℝ)) (X := (32023228034595451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251707064924759901/6250000000000000000 : ℝ) ≤ (2500166284117611/2500000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (6251707064924759901/6250000000000000000 : ℝ)^2048 ≤ (2500166284117611/2500000000000000 : ℝ)^8409 := by
      have hnat : (6251707064924759901 : ℕ)^2048*2500000000000000^8409 ≤ 2500166284117611^8409*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251707064924759901 6250000000000000000 2500166284117611 2500000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500166284117611/2500000000000000 : ℝ)) (X := (6251707064924759901/6250000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045679747432674659/100000000000000000000 : ℝ) ≤ (1250139041449377/1250000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (100045679747432674659/100000000000000000000 : ℝ)^2048 ≤ (1250139041449377/1250000000000000 : ℝ)^8409 := by
      have hnat : (100045679747432674659 : ℕ)^2048*1250000000000000^8409 ≤ 1250139041449377^8409*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045679747432674659 100000000000000000000 1250139041449377 1250000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250139041449377/1250000000000000 : ℝ)) (X := (100045679747432674659/100000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032023228034595451/50000000000000000000 : ℝ) ≤ (2500389881679897/2500000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (50032023228034595451/50000000000000000000 : ℝ)^2048 ≤ (2500389881679897/2500000000000000 : ℝ)^8409 := by
      have hnat : (50032023228034595451 : ℕ)^2048*2500000000000000^8409 ≤ 2500389881679897^8409*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032023228034595451 50000000000000000000 2500389881679897 2500000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500389881679897/2500000000000000 : ℝ)) (X := (50032023228034595451/50000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1707064924759901/12500000000000000000 : ℝ) ≤ ((6600379187863998237/6602500000000000000 : ℝ)+2*(111798781143/66025000000000 : ℝ)*(11449/100000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (6600379187863998237/6602500000000000000 : ℝ)+2*(111798781143/66025000000000 : ℝ)*(11449/100000 : ℝ)=(2500166284117611/2500000000000000 : ℝ) by norm_num, show 1+2*(1707064924759901/12500000000000000000 : ℝ)=(6251707064924759901/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32023228034595451/100000000000000000000 : ℝ)+(1707064924759901/12500000000000000000 : ℝ) ≤ ((6600379187863998237/6602500000000000000 : ℝ)+(111798781143/66025000000000 : ℝ)*((1409/10000 : ℝ)+(11449/100000 : ℝ)))^(8409/2048 : ℝ) := by
    rw [show (6600379187863998237/6602500000000000000 : ℝ)+(111798781143/66025000000000 : ℝ)*((1409/10000 : ℝ)+(11449/100000 : ℝ))=(1250139041449377/1250000000000000 : ℝ) by norm_num, show 1+(32023228034595451/100000000000000000000 : ℝ)+(1707064924759901/12500000000000000000 : ℝ)=(100045679747432674659/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32023228034595451/100000000000000000000 : ℝ) ≤ ((6600379187863998237/6602500000000000000 : ℝ)+2*(111798781143/66025000000000 : ℝ)*(1409/10000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (6600379187863998237/6602500000000000000 : ℝ)+2*(111798781143/66025000000000 : ℝ)*(1409/10000 : ℝ)=(2500389881679897/2500000000000000 : ℝ) by norm_num, show 1+2*(32023228034595451/100000000000000000000 : ℝ)=(50032023228034595451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6600379187863998237/6602500000000000000 : ℝ)*(X 1 0+X 2 0)+(111798781143/66025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (6600379187863998237/6602500000000000000 : ℝ)) (alpha := (111798781143/66025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6600379187863998237/6602500000000000000 : ℝ)*(X 0 1+X 2 1)+(111798781143/66025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (6600379187863998237/6602500000000000000 : ℝ)) (alpha := (111798781143/66025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6600379187863998237/6602500000000000000 : ℝ)*(X 0 2+X 1 2)+(111798781143/66025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (6600379187863998237/6602500000000000000 : ℝ)) (alpha := (111798781143/66025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2007061653/10000000000 : ℝ)*X 0 0+(2687606999/5000000000 : ℝ)*X 0 1+(5375214191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296615793/10000000000 : ℝ)*X 1 0+(-528458081/2500000000 : ℝ)*X 1 1+(1343803523/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296615813/10000000000 : ℝ)*X 2 0+(2687607023/5000000000 : ℝ)*X 2 1+(-52845809/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4460982497/10000000000 : ℝ)*X 0 0+(860577943/2000000000 : ℝ)*X 0 1+(4302889679/10000000000 : ℝ)*X 0 2+(4460982497/10000000000 : ℝ)*X 1 0+(860577943/2000000000 : ℝ)*X 1 1+(4302889679/10000000000 : ℝ)*X 1 2+(4460982497/10000000000 : ℝ)*X 2 0+(860577943/2000000000 : ℝ)*X 2 1+(4302889679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-225738231/1000000000 : ℝ)*X 0 0+(2641012731/5000000000 : ℝ)*X 0 1+(5282025533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362343783/10000000000 : ℝ)*X 1 0+(-215070511/1000000000 : ℝ)*X 1 1+(2641012629/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((536234319/1000000000 : ℝ)*X 2 0+(5282025711/10000000000 : ℝ)*X 2 1+(-2150705301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1061764029/2500000000 : ℝ)*X 0 0+(4409832661/10000000000 : ℝ)*X 0 1+(4409832563/10000000000 : ℝ)*X 0 2+(1061764029/2500000000 : ℝ)*X 1 0+(4409832661/10000000000 : ℝ)*X 1 1+(4409832563/10000000000 : ℝ)*X 1 2+(1061764029/2500000000 : ℝ)*X 2 0+(4409832661/10000000000 : ℝ)*X 2 1+(4409832563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2204954207/10000000000 : ℝ)*X 0 0+(1304626859/2500000000 : ℝ)*X 0 1+(26924131/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((661229149/1250000000 : ℝ)*X 1 0+(-527490321/2500000000 : ℝ)*X 1 1+(5384826083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322458287/2500000000 : ℝ)*X 2 0+(1346206573/2500000000 : ℝ)*X 2 1+(-1054980531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2241387789/5000000000 : ℝ)*X 0 0+(4291852563/10000000000 : ℝ)*X 0 1+(2145926353/5000000000 : ℝ)*X 0 2+(2241387789/5000000000 : ℝ)*X 1 0+(4291852563/10000000000 : ℝ)*X 1 1+(2145926353/5000000000 : ℝ)*X 1 2+(2241387789/5000000000 : ℝ)*X 2 0+(4291852563/10000000000 : ℝ)*X 2 1+(2145926353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2059764197/10000000000 : ℝ)*X 0 0+(1359376773/2500000000 : ℝ)*X 0 1+(41202777/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684016749/5000000000 : ℝ)*X 1 0+(-2153841673/10000000000 : ℝ)*X 1 1+(2636977783/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342008361/2500000000 : ℝ)*X 2 0+(20601389/39062500 : ℝ)*X 2 1+(-2153841721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2114149849/5000000000 : ℝ)*X 0 0+(4419088203/10000000000 : ℝ)*X 0 1+(2209544141/5000000000 : ℝ)*X 0 2+(2114149849/5000000000 : ℝ)*X 1 0+(4419088203/10000000000 : ℝ)*X 1 1+(2209544141/5000000000 : ℝ)*X 1 2+(2114149849/5000000000 : ℝ)*X 2 0+(4419088203/10000000000 : ℝ)*X 2 1+(2209544141/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31121/50000 : ℝ) ≤ (-102734064892561695771074864974827/165062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180007103/100000000000000 : ℝ)*(upper1) + (68579647/25000000000000 : ℝ)*(lower4) + (5683267/20000000000000 : ℝ)*(upper5) + (1991421203161119/50000000000000 : ℝ)*(major0) + (1991421203161119/50000000000000 : ℝ)*(major1) + (1991421203161119/50000000000000 : ℝ)*(major2) + (4144339339/50000000000000 : ℝ)*(sp3) + (2673861531574927/50000000000000 : ℝ)*(sp4) + (534768223789163/10000000000000 : ℝ)*(sp5) + (1336901755745903/25000000000000 : ℝ)*(sp6) + (1319349640196117/50000000000000 : ℝ)*(sp7) + (27137827/4000000000000 : ℝ)*(sp12) + (20751851949/50000000000000 : ℝ)*(sp13) + (116718611917/100000000000000 : ℝ)*(sp14) + (41229805766733/1562500000000 : ℝ)*(f.failure) + (5347723741595529/100000000000000 : ℝ)*(f.sum) + (4189251188839/13205000000000000000000000000 : ℝ)*base66 + (113289785318323537/17375000000000000000000000000000 : ℝ)*base67 + (201631339672573537/17375000000000000000000000000000 : ℝ)*base69 + (257791535422323537/17375000000000000000000000000000 : ℝ)*base71 + (41301894250093/6602500000000000000000000000 : ℝ)*base73 + (248531471695823537/17375000000000000000000000000000 : ℝ)*base75 + (113451451944073537/17375000000000000000000000000000 : ℝ)*base77 + (99251949234823537/17375000000000000000000000000000 : ℝ)*base79 + (30356838288539/13205000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (39039/19531250000000000000 : ℝ)*base90 + (39039/19531250000000000000 : ℝ)*base92 + (39039/19531250000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59357/100000 : ℝ) ≤ (7838474178962492169091543299/13205000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4133179/20000000000000 : ℝ)*(upper1) + (82228033/100000000000000 : ℝ)*(upper2) + (4495381/20000000000000 : ℝ)*(upper3) + (33428847/50000000000000 : ℝ)*(upper4) + (28997739/100000000000000 : ℝ)*(upper5) + (4048229632781399/100000000000000 : ℝ)*(major0) + (4048229632781399/100000000000000 : ℝ)*(major1) + (4048229632781399/100000000000000 : ℝ)*(major2) + (539463935135491/10000000000000 : ℝ)*(sp0) + (1348661201128347/25000000000000 : ℝ)*(sp1) + (674325779519171/12500000000000 : ℝ)*(sp2) + (268202782927113/10000000000000 : ℝ)*(sp3) + (1928418001/5000000000000 : ℝ)*(sp10) + (5453158479/100000000000000 : ℝ)*(sp12) + (268202782927113/10000000000000 : ℝ)*(f.failure) + (1348661201128347/25000000000000 : ℝ)*(f.sum) + (25682001433257/13205000000000000000000000000 : ℝ)*base66 + (243449709029925977/34750000000000000000000000000000 : ℝ)*base67 + (274152072853574023/34750000000000000000000000000000 : ℝ)*base70 + (43628975056074023/34750000000000000000000000000000 : ℝ)*base72 + (23827269061719/6602500000000000000000000000 : ℝ)*base73 + (131866077091925977/34750000000000000000000000000000 : ℝ)*base75 + (755142677541074023/34750000000000000000000000000000 : ℝ)*base78 + (40475323209925977/34750000000000000000000000000000 : ℝ)*base79 + (43468469955761/6602500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (21919/7812500000000000000 : ℝ)*base90 + (21919/7812500000000000000 : ℝ)*base92 + (21919/7812500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (16007/20000 : ℝ) ≤ (132111511852473107176642748243073/165062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13239257/50000000000000 : ℝ)*(lower1) + (48771489/50000000000000 : ℝ)*(lower3) + (65063127/100000000000000 : ℝ)*(upper4) + (4515379139021957/100000000000000 : ℝ)*(major0) + (4515379139021957/100000000000000 : ℝ)*(major1) + (4515379139021957/100000000000000 : ℝ)*(major2) + (43357763/5000000000000 : ℝ)*(sp0) + (1613668923/100000000000000 : ℝ)*(sp1) + (136543468517/100000000000000 : ℝ)*(sp2) + (35457221453/100000000000000 : ℝ)*(sp3) + (300627760497/5000000000 : ℝ)*(sp8) + (3006277231713169/50000000000000 : ℝ)*(sp9) + (6012419533626743/100000000000000 : ℝ)*(sp10) + (747871913782229/25000000000000 : ℝ)*(sp11) + (299152311235037/10000000000000 : ℝ)*(f.failure) + (300627803854763/5000000000000 : ℝ)*(f.sum) + (39363042864559/13205000000000000000000000000 : ℝ)*base65 + (604565993651928411/34750000000000000000000000000000 : ℝ)*base67 + (3195408265516928411/34750000000000000000000000000000 : ℝ)*base69 + (206782870802178411/34750000000000000000000000000000 : ℝ)*base71 + (45014706935809/13205000000000000000000000000 : ℝ)*base73 + (882967879755571589/34750000000000000000000000000000 : ℝ)*base76 + (562761021164678411/34750000000000000000000000000000 : ℝ)*base77 + (505433026436428411/34750000000000000000000000000000 : ℝ)*base79 + (1405070402048481/13205000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (60219/7812500000000000000 : ℝ)*base89 + (60219/7812500000000000000 : ℝ)*base91 + (60219/7812500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83291/100000 : ℝ) ≤ (-4296183254808557702880566898657/5158203125000000000000000000000 : ℝ) := by norm_num
    linear_combination (59095347/100000000000000 : ℝ)*(lower0) + (30067377/50000000000000 : ℝ)*(lower1) + (11237759/25000000000000 : ℝ)*(lower4) + (284421297353649/6250000000000 : ℝ)*(major0) + (284421297353649/6250000000000 : ℝ)*(major1) + (284421297353649/6250000000000 : ℝ)*(major2) + (1840832719/12500000000000 : ℝ)*(sp0) + (43991096667/25000000000000 : ℝ)*(sp5) + (98460079799/50000000000000 : ℝ)*(sp6) + (540369699/5000000000000 : ℝ)*(sp7) + (6114278732415107/100000000000000 : ℝ)*(sp12) + (382132343418137/6250000000000 : ℝ)*(sp13) + (6114096538917261/100000000000000 : ℝ)*(sp14) + (188433752407961/6250000000000 : ℝ)*(sp15) + (602990169184271/20000000000000 : ℝ)*(f.failure) + (305714672953843/5000000000000 : ℝ)*(f.sum) + (124070763465917/13205000000000000000000000000 : ℝ)*base66 + (14964386918662727/2171875000000000000000000000000 : ℝ)*base67 + (36031127559725227/2171875000000000000000000000000 : ℝ)*base69 + (2914447554149773/2171875000000000000000000000000 : ℝ)*base72 + (51587407958453/3301250000000000000000000000 : ℝ)*base74 + (15677026148975227/2171875000000000000000000000000 : ℝ)*base75 + (13810341190912727/2171875000000000000000000000000 : ℝ)*base77 + (25688418787131477/2171875000000000000000000000000 : ℝ)*base79 + (106823839733917/13205000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (18613/3906250000000000000 : ℝ)*base89 + (18613/3906250000000000000 : ℝ)*base91 + (18613/3906250000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1217_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59357/100000 : ℝ) else (16007/20000 : ℝ) ≤ X j i ∧ X j i ≤ (83291/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1217_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1217_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59357/100000 : ℝ) else (16007/20000 : ℝ) ≤ X j i ∧ X j i ≤ (83291/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1217_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1217_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59357/100000 : ℝ) else (16007/20000 : ℝ) ≤ X j i ∧ X j i ≤ (83291/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1217_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
