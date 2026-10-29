-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1459_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:47.977979+00:00
-- url     : https://prove2.me/submissions/bc933255-eb64-43ba-857e-9805ef29d349

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
theorem support_rectangle_w1459_s3_0 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1946160131/10000000000 : ℝ)*x 0 + (5414363347/10000000000 : ℝ)*x 1 + (1048086437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1946160131/10000000000 : ℝ)^4419 ≤ (11879019387091/100000000000000 : ℝ)^3395 := by
    have hnat : (1946160131 : ℕ)^4419*100000000000000^3395 ≤ 11879019387091^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946160131 10000000000 11879019387091 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414363347/10000000000 : ℝ)^4419 ≤ (44996626514517/100000000000000 : ℝ)^3395 := by
    have hnat : (5414363347 : ℕ)^4419*100000000000000^3395 ≤ 44996626514517^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414363347 10000000000 44996626514517 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048086437/2000000000 : ℝ)^4419 ≤ (43124354086239/100000000000000 : ℝ)^3395 := by
    have hnat : (1048086437 : ℕ)^4419*100000000000000^3395 ≤ 43124354086239^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048086437 2000000000 43124354086239 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1946160131/10000000000 : ℝ), (5414363347/10000000000 : ℝ), (1048086437/2000000000 : ℝ)] ![(11879019387091/100000000000000 : ℝ), (44996626514517/100000000000000 : ℝ), (43124354086239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1946160131/10000000000 : ℝ)|^4419 ≤ (11879019387091/100000000000000 : ℝ)^3395
        have hw : |(-1946160131/10000000000 : ℝ)|=(1946160131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414363347/10000000000 : ℝ)|^4419 ≤ (44996626514517/100000000000000 : ℝ)^3395
        have hw : |(5414363347/10000000000 : ℝ)|=(5414363347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048086437/2000000000 : ℝ)|^4419 ≤ (43124354086239/100000000000000 : ℝ)^3395
        have hw : |(1048086437/2000000000 : ℝ)|=(1048086437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s3_1 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348672577/10000000000 : ℝ)*x 0 + (-2034833483/10000000000 : ℝ)*x 1 + (5240432333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348672577/10000000000 : ℝ)^4419 ≤ (5535917132371/12500000000000 : ℝ)^3395 := by
    have hnat : (5348672577 : ℕ)^4419*12500000000000^3395 ≤ 5535917132371^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348672577 10000000000 5535917132371 12500000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034833483/10000000000 : ℝ)^4419 ≤ (3147076811409/25000000000000 : ℝ)^3395 := by
    have hnat : (2034833483 : ℕ)^4419*25000000000000^3395 ≤ 3147076811409^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034833483 10000000000 3147076811409 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240432333/10000000000 : ℝ)^4419 ≤ (21562177835751/50000000000000 : ℝ)^3395 := by
    have hnat : (5240432333 : ℕ)^4419*50000000000000^3395 ≤ 21562177835751^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240432333 10000000000 21562177835751 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348672577/10000000000 : ℝ), (-2034833483/10000000000 : ℝ), (5240432333/10000000000 : ℝ)] ![(5535917132371/12500000000000 : ℝ), (3147076811409/25000000000000 : ℝ), (21562177835751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348672577/10000000000 : ℝ)|^4419 ≤ (5535917132371/12500000000000 : ℝ)^3395
        have hw : |(5348672577/10000000000 : ℝ)|=(5348672577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2034833483/10000000000 : ℝ)|^4419 ≤ (3147076811409/25000000000000 : ℝ)^3395
        have hw : |(-2034833483/10000000000 : ℝ)|=(2034833483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240432333/10000000000 : ℝ)|^4419 ≤ (21562177835751/50000000000000 : ℝ)^3395
        have hw : |(5240432333/10000000000 : ℝ)|=(5240432333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s3_2 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337167949/2500000000 : ℝ)*x 0 + (1310108111/2500000000 : ℝ)*x 1 + (-1017417191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337167949/2500000000 : ℝ)^4419 ≤ (22143664320873/50000000000000 : ℝ)^3395 := by
    have hnat : (1337167949 : ℕ)^4419*50000000000000^3395 ≤ 22143664320873^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337167949 2500000000 22143664320873 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310108111/2500000000 : ℝ)^4419 ≤ (862487137209/2000000000000 : ℝ)^3395 := by
    have hnat : (1310108111 : ℕ)^4419*2000000000000^3395 ≤ 862487137209^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310108111 2500000000 862487137209 2000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1017417191/5000000000 : ℝ)^4419 ≤ (125883144847/1000000000000 : ℝ)^3395 := by
    have hnat : (1017417191 : ℕ)^4419*1000000000000^3395 ≤ 125883144847^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017417191 5000000000 125883144847 1000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337167949/2500000000 : ℝ), (1310108111/2500000000 : ℝ), (-1017417191/5000000000 : ℝ)] ![(22143664320873/50000000000000 : ℝ), (862487137209/2000000000000 : ℝ), (125883144847/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337167949/2500000000 : ℝ)|^4419 ≤ (22143664320873/50000000000000 : ℝ)^3395
        have hw : |(1337167949/2500000000 : ℝ)|=(1337167949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310108111/2500000000 : ℝ)|^4419 ≤ (862487137209/2000000000000 : ℝ)^3395
        have hw : |(1310108111/2500000000 : ℝ)|=(1310108111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1017417191/5000000000 : ℝ)|^4419 ≤ (125883144847/1000000000000 : ℝ)^3395
        have hw : |(-1017417191/5000000000 : ℝ)|=(1017417191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s3_3 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148192447/5000000000 : ℝ)*x 0 + (164396721/400000000 : ℝ)*x 1 + (898065329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148192447/5000000000 : ℝ)^4419 ≤ (6659931268941/20000000000000 : ℝ)^3395 := by
    have hnat : (2148192447 : ℕ)^4419*20000000000000^3395 ≤ 6659931268941^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148192447 5000000000 6659931268941 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164396721/400000000 : ℝ)^4419 ≤ (31430949866959/100000000000000 : ℝ)^3395 := by
    have hnat : (164396721 : ℕ)^4419*100000000000000^3395 ≤ 31430949866959^3395*400000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164396721 400000000 31430949866959 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898065329/2000000000 : ℝ)^4419 ≤ (881734844397/2500000000000 : ℝ)^3395 := by
    have hnat : (898065329 : ℕ)^4419*2500000000000^3395 ≤ 881734844397^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898065329 2000000000 881734844397 2500000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148192447/5000000000 : ℝ), (164396721/400000000 : ℝ), (898065329/2000000000 : ℝ)] ![(6659931268941/20000000000000 : ℝ), (31430949866959/100000000000000 : ℝ), (881734844397/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148192447/5000000000 : ℝ)|^4419 ≤ (6659931268941/20000000000000 : ℝ)^3395
        have hw : |(2148192447/5000000000 : ℝ)|=(2148192447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164396721/400000000 : ℝ)|^4419 ≤ (31430949866959/100000000000000 : ℝ)^3395
        have hw : |(164396721/400000000 : ℝ)|=(164396721/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898065329/2000000000 : ℝ)|^4419 ≤ (881734844397/2500000000000 : ℝ)^3395
        have hw : |(898065329/2000000000 : ℝ)|=(898065329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s3_4 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-973087001/5000000000 : ℝ)*x 0 + (2620559941/5000000000 : ℝ)*x 1 + (216546887/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (973087001/5000000000 : ℝ)^4419 ≤ (11879129590361/100000000000000 : ℝ)^3395 := by
    have hnat : (973087001 : ℕ)^4419*100000000000000^3395 ≤ 11879129590361^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973087001 5000000000 11879129590361 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620559941/5000000000 : ℝ)^4419 ≤ (43131720319129/100000000000000 : ℝ)^3395 := by
    have hnat : (2620559941 : ℕ)^4419*100000000000000^3395 ≤ 43131720319129^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620559941 5000000000 43131720319129 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216546887/400000000 : ℝ)^4419 ≤ (2249457503981/5000000000000 : ℝ)^3395 := by
    have hnat : (216546887 : ℕ)^4419*5000000000000^3395 ≤ 2249457503981^3395*400000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216546887 400000000 2249457503981 5000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-973087001/5000000000 : ℝ), (2620559941/5000000000 : ℝ), (216546887/400000000 : ℝ)] ![(11879129590361/100000000000000 : ℝ), (43131720319129/100000000000000 : ℝ), (2249457503981/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-973087001/5000000000 : ℝ)|^4419 ≤ (11879129590361/100000000000000 : ℝ)^3395
        have hw : |(-973087001/5000000000 : ℝ)|=(973087001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620559941/5000000000 : ℝ)|^4419 ≤ (43131720319129/100000000000000 : ℝ)^3395
        have hw : |(2620559941/5000000000 : ℝ)|=(2620559941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216546887/400000000 : ℝ)|^4419 ≤ (2249457503981/5000000000000 : ℝ)^3395
        have hw : |(216546887/400000000 : ℝ)|=(216546887/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s3_5 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165728947/312500000 : ℝ)*x 0 + (-232699323/1250000000 : ℝ)*x 1 + (2706836079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165728947/312500000 : ℝ)^4419 ≤ (21899621994439/50000000000000 : ℝ)^3395 := by
    have hnat : (165728947 : ℕ)^4419*50000000000000^3395 ≤ 21899621994439^3395*312500000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165728947 312500000 21899621994439 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232699323/1250000000 : ℝ)^4419 ≤ (11211606099647/100000000000000 : ℝ)^3395 := by
    have hnat : (232699323 : ℕ)^4419*100000000000000^3395 ≤ 11211606099647^3395*1250000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232699323 1250000000 11211606099647 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706836079/5000000000 : ℝ)^4419 ≤ (22494574947867/50000000000000 : ℝ)^3395 := by
    have hnat : (2706836079 : ℕ)^4419*50000000000000^3395 ≤ 22494574947867^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706836079 5000000000 22494574947867 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165728947/312500000 : ℝ), (-232699323/1250000000 : ℝ), (2706836079/5000000000 : ℝ)] ![(21899621994439/50000000000000 : ℝ), (11211606099647/100000000000000 : ℝ), (22494574947867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165728947/312500000 : ℝ)|^4419 ≤ (21899621994439/50000000000000 : ℝ)^3395
        have hw : |(165728947/312500000 : ℝ)|=(165728947/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-232699323/1250000000 : ℝ)|^4419 ≤ (11211606099647/100000000000000 : ℝ)^3395
        have hw : |(-232699323/1250000000 : ℝ)|=(232699323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706836079/5000000000 : ℝ)|^4419 ≤ (22494574947867/50000000000000 : ℝ)^3395
        have hw : |(2706836079/5000000000 : ℝ)|=(2706836079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s3_6 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303325277/10000000000 : ℝ)*x 0 + (676709119/1250000000 : ℝ)*x 1 + (-1861594897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303325277/10000000000 : ℝ)^4419 ≤ (2189961647439/5000000000000 : ℝ)^3395 := by
    have hnat : (5303325277 : ℕ)^4419*5000000000000^3395 ≤ 2189961647439^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303325277 10000000000 2189961647439 5000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676709119/1250000000 : ℝ)^4419 ≤ (44989158484299/100000000000000 : ℝ)^3395 := by
    have hnat : (676709119 : ℕ)^4419*100000000000000^3395 ≤ 44989158484299^3395*1250000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676709119 1250000000 44989158484299 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1861594897/10000000000 : ℝ)^4419 ≤ (11211608553289/100000000000000 : ℝ)^3395 := by
    have hnat : (1861594897 : ℕ)^4419*100000000000000^3395 ≤ 11211608553289^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861594897 10000000000 11211608553289 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303325277/10000000000 : ℝ), (676709119/1250000000 : ℝ), (-1861594897/10000000000 : ℝ)] ![(2189961647439/5000000000000 : ℝ), (44989158484299/100000000000000 : ℝ), (11211608553289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303325277/10000000000 : ℝ)|^4419 ≤ (2189961647439/5000000000000 : ℝ)^3395
        have hw : |(5303325277/10000000000 : ℝ)|=(5303325277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676709119/1250000000 : ℝ)|^4419 ≤ (44989158484299/100000000000000 : ℝ)^3395
        have hw : |(676709119/1250000000 : ℝ)|=(676709119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1861594897/10000000000 : ℝ)|^4419 ≤ (11211608553289/100000000000000 : ℝ)^3395
        have hw : |(-1861594897/10000000000 : ℝ)|=(1861594897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s3_7 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (859283159/2000000000 : ℝ)*x 0 + (1122206143/2500000000 : ℝ)*x 1 + (822285853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859283159/2000000000 : ℝ)^4419 ≤ (6659993617123/20000000000000 : ℝ)^3395 := by
    have hnat : (859283159 : ℕ)^4419*20000000000000^3395 ≤ 6659993617123^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859283159 2000000000 6659993617123 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122206143/2500000000 : ℝ)^4419 ≤ (1762701897089/5000000000000 : ℝ)^3395 := by
    have hnat : (1122206143 : ℕ)^4419*5000000000000^3395 ≤ 1762701897089^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122206143 2500000000 1762701897089 5000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (822285853/2000000000 : ℝ)^4419 ≤ (31445993962741/100000000000000 : ℝ)^3395 := by
    have hnat : (822285853 : ℕ)^4419*100000000000000^3395 ≤ 31445993962741^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      822285853 2000000000 31445993962741 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859283159/2000000000 : ℝ), (1122206143/2500000000 : ℝ), (822285853/2000000000 : ℝ)] ![(6659993617123/20000000000000 : ℝ), (1762701897089/5000000000000 : ℝ), (31445993962741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859283159/2000000000 : ℝ)|^4419 ≤ (6659993617123/20000000000000 : ℝ)^3395
        have hw : |(859283159/2000000000 : ℝ)|=(859283159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122206143/2500000000 : ℝ)|^4419 ≤ (1762701897089/5000000000000 : ℝ)^3395
        have hw : |(1122206143/2500000000 : ℝ)|=(1122206143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(822285853/2000000000 : ℝ)|^4419 ≤ (31445993962741/100000000000000 : ℝ)^3395
        have hw : |(822285853/2000000000 : ℝ)|=(822285853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1459_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (491/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (703/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14933/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (491/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5261/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (491/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5261/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (491/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5261/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (491/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5261/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (491/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5261/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (491/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5261/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5261/50000 : ℝ) ^ (2209/512 : ℝ) ≤ (3018971046089467/50000000000000000000 : ℝ) := by
    have hpowers : (5261/50000 : ℝ)^2209 ≤ (3018971046089467/50000000000000000000 : ℝ)^512 := by
      have hnat : (5261 : ℕ)^2209*50000000000000000000^512 ≤ 3018971046089467^512*50000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5261 50000 3018971046089467 50000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5261/50000 : ℝ)) (X := (3018971046089467/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hpowhi : (491/3125 : ℝ) ^ (2209/512 : ℝ) ≤ (17027400855184079/50000000000000000000 : ℝ) := by
    have hpowers : (491/3125 : ℝ)^2209 ≤ (17027400855184079/50000000000000000000 : ℝ)^512 := by
      have hnat : (491 : ℕ)^2209*50000000000000000000^512 ≤ 17027400855184079^512*3125^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        491 3125 17027400855184079 50000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (491/3125 : ℝ)) (X := (17027400855184079/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003018971046089467/25000000000000000000 : ℝ) ≤ (2000055976151497/2000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (25003018971046089467/25000000000000000000 : ℝ)^512 ≤ (2000055976151497/2000000000000000 : ℝ)^2209 := by
      have hnat : (25003018971046089467 : ℕ)^512*2000000000000000^2209 ≤ 2000055976151497^2209*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003018971046089467 25000000000000000000 2000055976151497 2000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000055976151497/2000000000000000 : ℝ)) (X := (25003018971046089467/25000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010023185950636773/25000000000000000000 : ℝ) ≤ (1250116140359509/1250000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (25010023185950636773/25000000000000000000 : ℝ)^512 ≤ (1250116140359509/1250000000000000 : ℝ)^2209 := by
      have hnat : (25010023185950636773 : ℕ)^512*1250000000000000^2209 ≤ 1250116140359509^2209*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010023185950636773 25000000000000000000 1250116140359509 1250000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250116140359509/1250000000000000 : ℝ)) (X := (25010023185950636773/25000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017027400855184079/25000000000000000000 : ℝ) ≤ (10001578364994659/10000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (25017027400855184079/25000000000000000000 : ℝ)^512 ≤ (10001578364994659/10000000000000000 : ℝ)^2209 := by
      have hnat : (25017027400855184079 : ℕ)^512*10000000000000000^2209 ≤ 10001578364994659^2209*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017027400855184079 25000000000000000000 10001578364994659 10000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001578364994659/10000000000000000 : ℝ)) (X := (25017027400855184079/25000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3018971046089467/50000000000000000000 : ℝ) ≤ ((8647964988331300387/8650000000000000000 : ℝ)+2*(216414039529/173000000000000 : ℝ)*(5261/50000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (8647964988331300387/8650000000000000000 : ℝ)+2*(216414039529/173000000000000 : ℝ)*(5261/50000 : ℝ)=(2000055976151497/2000000000000000 : ℝ) by norm_num, show 1+2*(3018971046089467/50000000000000000000 : ℝ)=(25003018971046089467/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17027400855184079/50000000000000000000 : ℝ)+(3018971046089467/50000000000000000000 : ℝ) ≤ ((8647964988331300387/8650000000000000000 : ℝ)+(216414039529/173000000000000 : ℝ)*((491/3125 : ℝ)+(5261/50000 : ℝ)))^(2209/512 : ℝ) := by
    rw [show (8647964988331300387/8650000000000000000 : ℝ)+(216414039529/173000000000000 : ℝ)*((491/3125 : ℝ)+(5261/50000 : ℝ))=(1250116140359509/1250000000000000 : ℝ) by norm_num, show 1+(17027400855184079/50000000000000000000 : ℝ)+(3018971046089467/50000000000000000000 : ℝ)=(25010023185950636773/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17027400855184079/50000000000000000000 : ℝ) ≤ ((8647964988331300387/8650000000000000000 : ℝ)+2*(216414039529/173000000000000 : ℝ)*(491/3125 : ℝ))^(2209/512 : ℝ) := by
    rw [show (8647964988331300387/8650000000000000000 : ℝ)+2*(216414039529/173000000000000 : ℝ)*(491/3125 : ℝ)=(10001578364994659/10000000000000000 : ℝ) by norm_num, show 1+2*(17027400855184079/50000000000000000000 : ℝ)=(25017027400855184079/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8647964988331300387/8650000000000000000 : ℝ)*(X 1 0+X 2 0)+(216414039529/173000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (5261/50000 : ℝ)) (hi := (491/3125 : ℝ)) (c := (8647964988331300387/8650000000000000000 : ℝ)) (alpha := (216414039529/173000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8647964988331300387/8650000000000000000 : ℝ)*(X 0 1+X 2 1)+(216414039529/173000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (5261/50000 : ℝ)) (hi := (491/3125 : ℝ)) (c := (8647964988331300387/8650000000000000000 : ℝ)) (alpha := (216414039529/173000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8647964988331300387/8650000000000000000 : ℝ)*(X 0 2+X 1 2)+(216414039529/173000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (5261/50000 : ℝ)) (hi := (491/3125 : ℝ)) (c := (8647964988331300387/8650000000000000000 : ℝ)) (alpha := (216414039529/173000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1946160131/10000000000 : ℝ)*X 0 0+(5414363347/10000000000 : ℝ)*X 0 1+(1048086437/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348672577/10000000000 : ℝ)*X 1 0+(-2034833483/10000000000 : ℝ)*X 1 1+(5240432333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337167949/2500000000 : ℝ)*X 2 0+(1310108111/2500000000 : ℝ)*X 2 1+(-1017417191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2148192447/5000000000 : ℝ)*X 0 0+(164396721/400000000 : ℝ)*X 0 1+(898065329/2000000000 : ℝ)*X 0 2+(2148192447/5000000000 : ℝ)*X 1 0+(164396721/400000000 : ℝ)*X 1 1+(898065329/2000000000 : ℝ)*X 1 2+(2148192447/5000000000 : ℝ)*X 2 0+(164396721/400000000 : ℝ)*X 2 1+(898065329/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-973087001/5000000000 : ℝ)*X 0 0+(2620559941/5000000000 : ℝ)*X 0 1+(216546887/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165728947/312500000 : ℝ)*X 1 0+(-232699323/1250000000 : ℝ)*X 1 1+(2706836079/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303325277/10000000000 : ℝ)*X 2 0+(676709119/1250000000 : ℝ)*X 2 1+(-1861594897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859283159/2000000000 : ℝ)*X 0 0+(1122206143/2500000000 : ℝ)*X 0 1+(822285853/2000000000 : ℝ)*X 0 2+(859283159/2000000000 : ℝ)*X 1 0+(1122206143/2500000000 : ℝ)*X 1 1+(822285853/2000000000 : ℝ)*X 1 2+(859283159/2000000000 : ℝ)*X 2 0+(1122206143/2500000000 : ℝ)*X 2 1+(822285853/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (933742846351937585463542067/108125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2522072809/100000000000000 : ℝ)*(base19) + (814973461/50000000000000 : ℝ)*(base23) + (2116323/3125000000000 : ℝ)*(upper2) + (80073159/20000000000000 : ℝ)*(upper3) + (2094579839112453/50000000000000 : ℝ)*(major0) + (2094579839112453/50000000000000 : ℝ)*(major1) + (2094579839112453/50000000000000 : ℝ)*(major2) + (2874737517675959/50000000000000 : ℝ)*(sp0) + (1437380901421569/25000000000000 : ℝ)*(sp1) + (2874751679914017/50000000000000 : ℝ)*(sp2) + (328596449313351/12500000000000 : ℝ)*(sp3) + (51092407167/100000000000000 : ℝ)*(sp4) + (2113798413/10000000000000 : ℝ)*(sp6) + (10673162421/50000000000000 : ℝ)*(sp7) + (52575858816633/2000000000000 : ℝ)*(f.failure) + (1149905225551817/20000000000000 : ℝ)*(f.sum) + (7990803294113/4325000000000000000000000000 : ℝ)*base66 + (4410218350467269311/432500000000000000000000000000000 : ℝ)*base67 + (4345523408434769311/432500000000000000000000000000000 : ℝ)*base69 + (1530496970242269311/432500000000000000000000000000000 : ℝ)*base71 + (5034071022937/4325000000000000000000000000 : ℝ)*base73 + (1855360174512269311/432500000000000000000000000000000 : ℝ)*base75 + (1265231822227269311/432500000000000000000000000000000 : ℝ)*base77 + (5862626753952730689/432500000000000000000000000000000 : ℝ)*base80 + (2974081411737/4325000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (243099/25000000000000000000 : ℝ)*base90 + (243099/25000000000000000000 : ℝ)*base92 + (243099/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130740940736314056817533/8650000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15079119/12500000000000 : ℝ)*(base19) + (99770967/50000000000000 : ℝ)*(upper2) + (45474169/100000000000000 : ℝ)*(upper3) + (80527831/25000000000000 : ℝ)*(lower4) + (29979943/25000000000000 : ℝ)*(upper5) + (4222531203378297/100000000000000 : ℝ)*(major0) + (4222531203378297/100000000000000 : ℝ)*(major1) + (4222531203378297/100000000000000 : ℝ)*(major2) + (421258223/20000000000000 : ℝ)*(sp2) + (593019873/100000000000000 : ℝ)*(sp3) + (5795327571353373/100000000000000 : ℝ)*(sp4) + (5795327450720421/100000000000000 : ℝ)*(sp5) + (5795325465062259/100000000000000 : ℝ)*(sp6) + (1324866869282341/50000000000000 : ℝ)*(sp7) + (662433582896139/25000000000000 : ℝ)*(f.failure) + (5795327571353373/100000000000000 : ℝ)*(f.sum) + (27467091215213/8650000000000000000000000000 : ℝ)*base65 + (7290641015134150939/865000000000000000000000000000000 : ℝ)*base67 + (5887444783759150939/865000000000000000000000000000000 : ℝ)*base69 + (35516572166469150939/865000000000000000000000000000000 : ℝ)*base71 + (18110082089863/8650000000000000000000000000 : ℝ)*base73 + (779319756435849061/865000000000000000000000000000000 : ℝ)*base76 + (5190379127165849061/865000000000000000000000000000000 : ℝ)*base78 + (2415689755195849061/865000000000000000000000000000000 : ℝ)*base80 + (54398998940813/8650000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3610983/312500000000000000000 : ℝ)*base89 + (3610983/312500000000000000000 : ℝ)*base91 + (3610983/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1459_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (491/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1459_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1459_s4_0 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1946921929/10000000000 : ℝ)*x 0 + (1351945609/2500000000 : ℝ)*x 1 + (2623255431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1946921929/10000000000 : ℝ)^4419 ≤ (74281700767/625000000000 : ℝ)^3395 := by
    have hnat : (1946921929 : ℕ)^4419*625000000000^3395 ≤ 74281700767^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946921929 10000000000 74281700767 625000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351945609/2500000000 : ℝ)^4419 ≤ (4492545222161/10000000000000 : ℝ)^3395 := by
    have hnat : (1351945609 : ℕ)^4419*10000000000000^3395 ≤ 4492545222161^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351945609 2500000000 4492545222161 10000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623255431/5000000000 : ℝ)^4419 ≤ (43189475636911/100000000000000 : ℝ)^3395 := by
    have hnat : (2623255431 : ℕ)^4419*100000000000000^3395 ≤ 43189475636911^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623255431 5000000000 43189475636911 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1946921929/10000000000 : ℝ), (1351945609/2500000000 : ℝ), (2623255431/5000000000 : ℝ)] ![(74281700767/625000000000 : ℝ), (4492545222161/10000000000000 : ℝ), (43189475636911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1946921929/10000000000 : ℝ)|^4419 ≤ (74281700767/625000000000 : ℝ)^3395
        have hw : |(-1946921929/10000000000 : ℝ)|=(1946921929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351945609/2500000000 : ℝ)|^4419 ≤ (4492545222161/10000000000000 : ℝ)^3395
        have hw : |(1351945609/2500000000 : ℝ)|=(1351945609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623255431/5000000000 : ℝ)|^4419 ≤ (43189475636911/100000000000000 : ℝ)^3395
        have hw : |(2623255431/5000000000 : ℝ)|=(2623255431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s4_1 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673483267/5000000000 : ℝ)*x 0 + (-405805383/2000000000 : ℝ)*x 1 + (5246511087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673483267/5000000000 : ℝ)^4419 ≤ (11067237768957/25000000000000 : ℝ)^3395 := by
    have hnat : (2673483267 : ℕ)^4419*25000000000000^3395 ≤ 11067237768957^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673483267 5000000000 11067237768957 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405805383/2000000000 : ℝ)^4419 ≤ (12541570858667/100000000000000 : ℝ)^3395 := by
    have hnat : (405805383 : ℕ)^4419*100000000000000^3395 ≤ 12541570858667^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405805383 2000000000 12541570858667 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246511087/10000000000 : ℝ)^4419 ≤ (43189478047783/100000000000000 : ℝ)^3395 := by
    have hnat : (5246511087 : ℕ)^4419*100000000000000^3395 ≤ 43189478047783^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246511087 10000000000 43189478047783 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673483267/5000000000 : ℝ), (-405805383/2000000000 : ℝ), (5246511087/10000000000 : ℝ)] ![(11067237768957/25000000000000 : ℝ), (12541570858667/100000000000000 : ℝ), (43189478047783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673483267/5000000000 : ℝ)|^4419 ≤ (11067237768957/25000000000000 : ℝ)^3395
        have hw : |(2673483267/5000000000 : ℝ)|=(2673483267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405805383/2000000000 : ℝ)|^4419 ≤ (12541570858667/100000000000000 : ℝ)^3395
        have hw : |(-405805383/2000000000 : ℝ)|=(405805383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246511087/10000000000 : ℝ)|^4419 ≤ (43189478047783/100000000000000 : ℝ)^3395
        have hw : |(5246511087/10000000000 : ℝ)|=(5246511087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s4_2 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346966203/10000000000 : ℝ)*x 0 + (41972091/80000000 : ℝ)*x 1 + (-81161079/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346966203/10000000000 : ℝ)^4419 ≤ (44268947508821/100000000000000 : ℝ)^3395 := by
    have hnat : (5346966203 : ℕ)^4419*100000000000000^3395 ≤ 44268947508821^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346966203 10000000000 44268947508821 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41972091/80000000 : ℝ)^4419 ≤ (43189481133699/100000000000000 : ℝ)^3395 := by
    have hnat : (41972091 : ℕ)^4419*100000000000000^3395 ≤ 43189481133699^3395*80000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41972091 80000000 43189481133699 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81161079/400000000 : ℝ)^4419 ≤ (783848208837/6250000000000 : ℝ)^3395 := by
    have hnat : (81161079 : ℕ)^4419*6250000000000^3395 ≤ 783848208837^3395*400000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81161079 400000000 783848208837 6250000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346966203/10000000000 : ℝ), (41972091/80000000 : ℝ), (-81161079/400000000 : ℝ)] ![(44268947508821/100000000000000 : ℝ), (43189481133699/100000000000000 : ℝ), (783848208837/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346966203/10000000000 : ℝ)|^4419 ≤ (44268947508821/100000000000000 : ℝ)^3395
        have hw : |(5346966203/10000000000 : ℝ)|=(5346966203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41972091/80000000 : ℝ)|^4419 ≤ (43189481133699/100000000000000 : ℝ)^3395
        have hw : |(41972091/80000000 : ℝ)|=(41972091/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-81161079/400000000 : ℝ)|^4419 ≤ (783848208837/6250000000000 : ℝ)^3395
        have hw : |(-81161079/400000000 : ℝ)|=(81161079/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s4_3 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4296852617/10000000000 : ℝ)*x 0 + (1030926373/2500000000 : ℝ)*x 1 + (1119106903/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296852617/10000000000 : ℝ)^4419 ≤ (8326093745647/25000000000000 : ℝ)^3395 := by
    have hnat : (4296852617 : ℕ)^4419*25000000000000^3395 ≤ 8326093745647^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296852617 10000000000 8326093745647 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030926373/2500000000 : ℝ)^4419 ≤ (31568263148599/100000000000000 : ℝ)^3395 := by
    have hnat : (1030926373 : ℕ)^4419*100000000000000^3395 ≤ 31568263148599^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030926373 2500000000 31568263148599 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119106903/2500000000 : ℝ)^4419 ≤ (17563680930177/50000000000000 : ℝ)^3395 := by
    have hnat : (1119106903 : ℕ)^4419*50000000000000^3395 ≤ 17563680930177^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119106903 2500000000 17563680930177 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296852617/10000000000 : ℝ), (1030926373/2500000000 : ℝ), (1119106903/2500000000 : ℝ)] ![(8326093745647/25000000000000 : ℝ), (31568263148599/100000000000000 : ℝ), (17563680930177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296852617/10000000000 : ℝ)|^4419 ≤ (8326093745647/25000000000000 : ℝ)^3395
        have hw : |(4296852617/10000000000 : ℝ)|=(4296852617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030926373/2500000000 : ℝ)|^4419 ≤ (31568263148599/100000000000000 : ℝ)^3395
        have hw : |(1030926373/2500000000 : ℝ)|=(1030926373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119106903/2500000000 : ℝ)|^4419 ≤ (17563680930177/50000000000000 : ℝ)^3395
        have hw : |(1119106903/2500000000 : ℝ)|=(1119106903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s4_4 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1946933749/10000000000 : ℝ)*x 0 + (5247101977/10000000000 : ℝ)*x 1 + (5407187989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1946933749/10000000000 : ℝ)^4419 ≤ (1485645755267/12500000000000 : ℝ)^3395 := by
    have hnat : (1946933749 : ℕ)^4419*12500000000000^3395 ≤ 1485645755267^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946933749 10000000000 1485645755267 12500000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247101977/10000000000 : ℝ)^4419 ≤ (43195809533041/100000000000000 : ℝ)^3395 := by
    have hnat : (5247101977 : ℕ)^4419*100000000000000^3395 ≤ 43195809533041^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247101977 10000000000 43195809533041 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407187989/10000000000 : ℝ)^4419 ≤ (4491902440601/10000000000000 : ℝ)^3395 := by
    have hnat : (5407187989 : ℕ)^4419*10000000000000^3395 ≤ 4491902440601^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407187989 10000000000 4491902440601 10000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1946933749/10000000000 : ℝ), (5247101977/10000000000 : ℝ), (5407187989/10000000000 : ℝ)] ![(1485645755267/12500000000000 : ℝ), (43195809533041/100000000000000 : ℝ), (4491902440601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1946933749/10000000000 : ℝ)|^4419 ≤ (1485645755267/12500000000000 : ℝ)^3395
        have hw : |(-1946933749/10000000000 : ℝ)|=(1946933749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247101977/10000000000 : ℝ)|^4419 ≤ (43195809533041/100000000000000 : ℝ)^3395
        have hw : |(5247101977/10000000000 : ℝ)|=(5247101977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407187989/10000000000 : ℝ)|^4419 ≤ (4491902440601/10000000000000 : ℝ)^3395
        have hw : |(5407187989/10000000000 : ℝ)|=(5407187989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s4_5 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652460297/5000000000 : ℝ)*x 0 + (-1868350127/10000000000 : ℝ)*x 1 + (270359399/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652460297/5000000000 : ℝ)^4419 ≤ (21908191573739/50000000000000 : ℝ)^3395 := by
    have hnat : (2652460297 : ℕ)^4419*50000000000000^3395 ≤ 21908191573739^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652460297 5000000000 21908191573739 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1868350127/10000000000 : ℝ)^4419 ≤ (11264592525183/100000000000000 : ℝ)^3395 := by
    have hnat : (1868350127 : ℕ)^4419*100000000000000^3395 ≤ 11264592525183^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868350127 10000000000 11264592525183 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270359399/500000000 : ℝ)^4419 ≤ (22459512154347/50000000000000 : ℝ)^3395 := by
    have hnat : (270359399 : ℕ)^4419*50000000000000^3395 ≤ 22459512154347^3395*500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270359399 500000000 22459512154347 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652460297/5000000000 : ℝ), (-1868350127/10000000000 : ℝ), (270359399/500000000 : ℝ)] ![(21908191573739/50000000000000 : ℝ), (11264592525183/100000000000000 : ℝ), (22459512154347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652460297/5000000000 : ℝ)|^4419 ≤ (21908191573739/50000000000000 : ℝ)^3395
        have hw : |(2652460297/5000000000 : ℝ)|=(2652460297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1868350127/10000000000 : ℝ)|^4419 ≤ (11264592525183/100000000000000 : ℝ)^3395
        have hw : |(-1868350127/10000000000 : ℝ)|=(1868350127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270359399/500000000 : ℝ)|^4419 ≤ (22459512154347/50000000000000 : ℝ)^3395
        have hw : |(270359399/500000000 : ℝ)|=(270359399/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s4_6 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663115081/1250000000 : ℝ)*x 0 + (1351796987/2500000000 : ℝ)*x 1 + (-934175049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663115081/1250000000 : ℝ)^4419 ≤ (21908191864011/50000000000000 : ℝ)^3395 := by
    have hnat : (663115081 : ℕ)^4419*50000000000000^3395 ≤ 21908191864011^3395*1250000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663115081 1250000000 21908191864011 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351796987/2500000000 : ℝ)^4419 ≤ (44919023962681/100000000000000 : ℝ)^3395 := by
    have hnat : (1351796987 : ℕ)^4419*100000000000000^3395 ≤ 44919023962681^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351796987 2500000000 44919023962681 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934175049/5000000000 : ℝ)^4419 ≤ (3520185093/31250000000 : ℝ)^3395 := by
    have hnat : (934175049 : ℕ)^4419*31250000000^3395 ≤ 3520185093^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934175049 5000000000 3520185093 31250000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663115081/1250000000 : ℝ), (1351796987/2500000000 : ℝ), (-934175049/5000000000 : ℝ)] ![(21908191864011/50000000000000 : ℝ), (44919023962681/100000000000000 : ℝ), (3520185093/31250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663115081/1250000000 : ℝ)|^4419 ≤ (21908191864011/50000000000000 : ℝ)^3395
        have hw : |(663115081/1250000000 : ℝ)|=(663115081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351796987/2500000000 : ℝ)|^4419 ≤ (44919023962681/100000000000000 : ℝ)^3395
        have hw : |(1351796987/2500000000 : ℝ)|=(1351796987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-934175049/5000000000 : ℝ)|^4419 ≤ (3520185093/31250000000 : ℝ)^3395
        have hw : |(-934175049/5000000000 : ℝ)|=(934175049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s4_7 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4296878087/10000000000 : ℝ)*x 0 + (2237567311/5000000000 : ℝ)*x 1 + (4125004981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296878087/10000000000 : ℝ)^4419 ≤ (8326157985479/25000000000000 : ℝ)^3395 := by
    have hnat : (4296878087 : ℕ)^4419*25000000000000^3395 ≤ 8326157985479^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296878087 10000000000 8326157985479 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237567311/5000000000 : ℝ)^4419 ≤ (8778538941181/25000000000000 : ℝ)^3395 := by
    have hnat : (2237567311 : ℕ)^4419*25000000000000^3395 ≤ 8778538941181^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237567311 5000000000 8778538941181 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4125004981/10000000000 : ℝ)^4419 ≤ (31581212276337/100000000000000 : ℝ)^3395 := by
    have hnat : (4125004981 : ℕ)^4419*100000000000000^3395 ≤ 31581212276337^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125004981 10000000000 31581212276337 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296878087/10000000000 : ℝ), (2237567311/5000000000 : ℝ), (4125004981/10000000000 : ℝ)] ![(8326157985479/25000000000000 : ℝ), (8778538941181/25000000000000 : ℝ), (31581212276337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296878087/10000000000 : ℝ)|^4419 ≤ (8326157985479/25000000000000 : ℝ)^3395
        have hw : |(4296878087/10000000000 : ℝ)|=(4296878087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237567311/5000000000 : ℝ)|^4419 ≤ (8778538941181/25000000000000 : ℝ)^3395
        have hw : |(2237567311/5000000000 : ℝ)|=(2237567311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4125004981/10000000000 : ℝ)|^4419 ≤ (31581212276337/100000000000000 : ℝ)^3395
        have hw : |(4125004981/10000000000 : ℝ)|=(4125004981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1459_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5689/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2959/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (703/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (703/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (703/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (703/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (703/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (703/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (703/6250 : ℝ) ^ (2209/512 : ℝ) ≤ (4026047552694583/50000000000000000000 : ℝ) := by
    have hpowers : (703/6250 : ℝ)^2209 ≤ (4026047552694583/50000000000000000000 : ℝ)^512 := by
      have hnat : (703 : ℕ)^2209*50000000000000000000^512 ≤ 4026047552694583^512*6250^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        703 6250 4026047552694583 50000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (703/6250 : ℝ)) (X := (4026047552694583/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14933/100000 : ℝ) ^ (2209/512 : ℝ) ≤ (13673076024493239/50000000000000000000 : ℝ) := by
    have hpowers : (14933/100000 : ℝ)^2209 ≤ (13673076024493239/50000000000000000000 : ℝ)^512 := by
      have hnat : (14933 : ℕ)^2209*50000000000000000000^512 ≤ 13673076024493239^512*100000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14933 100000 13673076024493239 50000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14933/100000 : ℝ)) (X := (13673076024493239/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004026047552694583/25000000000000000000 : ℝ) ≤ (10000373238361103/10000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (25004026047552694583/25000000000000000000 : ℝ)^512 ≤ (10000373238361103/10000000000000000 : ℝ)^2209 := by
      have hnat : (25004026047552694583 : ℕ)^512*10000000000000000^2209 ≤ 10000373238361103^2209*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004026047552694583 25000000000000000000 10000373238361103 10000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000373238361103/10000000000000000 : ℝ)) (X := (25004026047552694583/25000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008849561788593911/25000000000000000000 : ℝ) ≤ (625051271612663/625000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (25008849561788593911/25000000000000000000 : ℝ)^512 ≤ (625051271612663/625000000000000 : ℝ)^2209 := by
      have hnat : (25008849561788593911 : ℕ)^512*625000000000000^2209 ≤ 625051271612663^2209*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008849561788593911 25000000000000000000 625051271612663 625000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625051271612663/625000000000000 : ℝ)) (X := (25008849561788593911/25000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013673076024493239/25000000000000000000 : ℝ) ≤ (10001267453244113/10000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (25013673076024493239/25000000000000000000 : ℝ)^512 ≤ (10001267453244113/10000000000000000 : ℝ)^2209 := by
      have hnat : (25013673076024493239 : ℕ)^512*10000000000000000^2209 ≤ 10001267453244113^2209*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013673076024493239 25000000000000000000 10001267453244113 10000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001267453244113/10000000000000000 : ℝ)) (X := (25013673076024493239/25000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4026047552694583/50000000000000000000 : ℝ) ≤ ((1473652690174262723/1474000000000000000 : ℝ)+2*(89421488301/73700000000000 : ℝ)*(703/6250 : ℝ))^(2209/512 : ℝ) := by
    rw [show (1473652690174262723/1474000000000000000 : ℝ)+2*(89421488301/73700000000000 : ℝ)*(703/6250 : ℝ)=(10000373238361103/10000000000000000 : ℝ) by norm_num, show 1+2*(4026047552694583/50000000000000000000 : ℝ)=(25004026047552694583/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13673076024493239/50000000000000000000 : ℝ)+(4026047552694583/50000000000000000000 : ℝ) ≤ ((1473652690174262723/1474000000000000000 : ℝ)+(89421488301/73700000000000 : ℝ)*((14933/100000 : ℝ)+(703/6250 : ℝ)))^(2209/512 : ℝ) := by
    rw [show (1473652690174262723/1474000000000000000 : ℝ)+(89421488301/73700000000000 : ℝ)*((14933/100000 : ℝ)+(703/6250 : ℝ))=(625051271612663/625000000000000 : ℝ) by norm_num, show 1+(13673076024493239/50000000000000000000 : ℝ)+(4026047552694583/50000000000000000000 : ℝ)=(25008849561788593911/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13673076024493239/50000000000000000000 : ℝ) ≤ ((1473652690174262723/1474000000000000000 : ℝ)+2*(89421488301/73700000000000 : ℝ)*(14933/100000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (1473652690174262723/1474000000000000000 : ℝ)+2*(89421488301/73700000000000 : ℝ)*(14933/100000 : ℝ)=(10001267453244113/10000000000000000 : ℝ) by norm_num, show 1+2*(13673076024493239/50000000000000000000 : ℝ)=(25013673076024493239/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1473652690174262723/1474000000000000000 : ℝ)*(X 1 0+X 2 0)+(89421488301/73700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (1473652690174262723/1474000000000000000 : ℝ)) (alpha := (89421488301/73700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1473652690174262723/1474000000000000000 : ℝ)*(X 0 1+X 2 1)+(89421488301/73700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (1473652690174262723/1474000000000000000 : ℝ)) (alpha := (89421488301/73700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1473652690174262723/1474000000000000000 : ℝ)*(X 0 2+X 1 2)+(89421488301/73700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (1473652690174262723/1474000000000000000 : ℝ)) (alpha := (89421488301/73700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1946921929/10000000000 : ℝ)*X 0 0+(1351945609/2500000000 : ℝ)*X 0 1+(2623255431/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673483267/5000000000 : ℝ)*X 1 0+(-405805383/2000000000 : ℝ)*X 1 1+(5246511087/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346966203/10000000000 : ℝ)*X 2 0+(41972091/80000000 : ℝ)*X 2 1+(-81161079/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4296852617/10000000000 : ℝ)*X 0 0+(1030926373/2500000000 : ℝ)*X 0 1+(1119106903/2500000000 : ℝ)*X 0 2+(4296852617/10000000000 : ℝ)*X 1 0+(1030926373/2500000000 : ℝ)*X 1 1+(1119106903/2500000000 : ℝ)*X 1 2+(4296852617/10000000000 : ℝ)*X 2 0+(1030926373/2500000000 : ℝ)*X 2 1+(1119106903/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1946933749/10000000000 : ℝ)*X 0 0+(5247101977/10000000000 : ℝ)*X 0 1+(5407187989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652460297/5000000000 : ℝ)*X 1 0+(-1868350127/10000000000 : ℝ)*X 1 1+(270359399/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663115081/1250000000 : ℝ)*X 2 0+(1351796987/2500000000 : ℝ)*X 2 1+(-934175049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4296878087/10000000000 : ℝ)*X 0 0+(2237567311/5000000000 : ℝ)*X 0 1+(4125004981/10000000000 : ℝ)*X 0 2+(4296878087/10000000000 : ℝ)*X 1 0+(2237567311/5000000000 : ℝ)*X 1 1+(4125004981/10000000000 : ℝ)*X 1 2+(4296878087/10000000000 : ℝ)*X 2 0+(2237567311/5000000000 : ℝ)*X 2 1+(4125004981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (726028950486163127214478563/73700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (254632923/25000000000000 : ℝ)*(base19) + (665233467/100000000000000 : ℝ)*(base23) + (21660857/25000000000000 : ℝ)*(lower2) + (117654127/100000000000000 : ℝ)*(upper3) + (102982227/100000000000000 : ℝ)*(lower4) + (4517955945834009/100000000000000 : ℝ)*(major0) + (4517955945834009/100000000000000 : ℝ)*(major1) + (4517955945834009/100000000000000 : ℝ)*(major2) + (6200759996115119/100000000000000 : ℝ)*(sp0) + (6200790470652819/100000000000000 : ℝ)*(sp1) + (1550197705987761/25000000000000 : ℝ)*(sp2) + (1417553171712533/50000000000000 : ℝ)*(sp3) + (31493069393/100000000000000 : ℝ)*(sp4) + (3432671783/25000000000000 : ℝ)*(sp7) + (1417560037056099/50000000000000 : ℝ)*(f.failure) + (6200791489184511/100000000000000 : ℝ)*(f.sum) + (172129394421/3685000000000000000000000000 : ℝ)*base66 + (211469204966873493/147400000000000000000000000000000 : ℝ)*base68 + (1056481525000073493/147400000000000000000000000000000 : ℝ)*base70 + (403258292076273493/147400000000000000000000000000000 : ℝ)*base72 + (3655241265063/1842500000000000000000000000 : ℝ)*base74 + (1764334796105273493/147400000000000000000000000000000 : ℝ)*base76 + (2300120382852673493/147400000000000000000000000000000 : ℝ)*base78 + (538459250513873493/147400000000000000000000000000000 : ℝ)*base80 + (14260063712669/3685000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2222103/625000000000000000000 : ℝ)*base89 + (2222103/625000000000000000000 : ℝ)*base91 + (2222103/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24987627238966813104147/3685000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130099281/12500000000000 : ℝ)*(base19) + (1241091409/100000000000000 : ℝ)*(base23) + (4520273/4000000000000 : ℝ)*(upper3) + (61546789/100000000000000 : ℝ)*(lower4) + (156163777/100000000000000 : ℝ)*(upper5) + (4551363558329449/100000000000000 : ℝ)*(major0) + (4551363558329449/100000000000000 : ℝ)*(major1) + (4551363558329449/100000000000000 : ℝ)*(major2) + (22367150823/100000000000000 : ℝ)*(sp1) + (24978190517/100000000000000 : ℝ)*(sp2) + (3123321390068047/50000000000000 : ℝ)*(sp4) + (6246619372191023/100000000000000 : ℝ)*(sp5) + (780827070106771/12500000000000 : ℝ)*(sp6) + (2856084110492703/100000000000000 : ℝ)*(sp7) + (2856084110492703/100000000000000 : ℝ)*(f.failure) + (3123321390068047/50000000000000 : ℝ)*(f.sum) + (2823916011987/1842500000000000000000000000 : ℝ)*base65 + (1028090936092790373/147400000000000000000000000000000 : ℝ)*base68 + (662068362329790373/147400000000000000000000000000000 : ℝ)*base70 + (362972508079809627/147400000000000000000000000000000 : ℝ)*base71 + (11964586949351/3685000000000000000000000000 : ℝ)*base74 + (372870030324790373/147400000000000000000000000000000 : ℝ)*base76 + (288097336374409627/147400000000000000000000000000000 : ℝ)*base77 + (1183448503539809627/147400000000000000000000000000000 : ℝ)*base79 + (19181647672091/3685000000000000000000000000 : ℝ)*base82 + (2700691/1250000000000000000000 : ℝ)*base89 + (2700691/1250000000000000000000 : ℝ)*base91 + (2700691/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1459_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1459_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1459_s5_0 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38940627/200000000 : ℝ)*x 0 + (1081362361/2000000000 : ℝ)*x 1 + (1049481841/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38940627/200000000 : ℝ)^4419 ≤ (2971485391807/25000000000000 : ℝ)^3395 := by
    have hnat : (38940627 : ℕ)^4419*25000000000000^3395 ≤ 2971485391807^3395*200000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38940627 200000000 2971485391807 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081362361/2000000000 : ℝ)^4419 ≤ (22457478400223/50000000000000 : ℝ)^3395 := by
    have hnat : (1081362361 : ℕ)^4419*50000000000000^3395 ≤ 22457478400223^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081362361 2000000000 22457478400223 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049481841/2000000000 : ℝ)^4419 ≤ (43199101617467/100000000000000 : ℝ)^3395 := by
    have hnat : (1049481841 : ℕ)^4419*100000000000000^3395 ≤ 43199101617467^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049481841 2000000000 43199101617467 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38940627/200000000 : ℝ), (1081362361/2000000000 : ℝ), (1049481841/2000000000 : ℝ)] ![(2971485391807/25000000000000 : ℝ), (22457478400223/50000000000000 : ℝ), (43199101617467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38940627/200000000 : ℝ)|^4419 ≤ (2971485391807/25000000000000 : ℝ)^3395
        have hw : |(-38940627/200000000 : ℝ)|=(38940627/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081362361/2000000000 : ℝ)|^4419 ≤ (22457478400223/50000000000000 : ℝ)^3395
        have hw : |(1081362361/2000000000 : ℝ)|=(1081362361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049481841/2000000000 : ℝ)|^4419 ≤ (43199101617467/100000000000000 : ℝ)^3395
        have hw : |(1049481841/2000000000 : ℝ)|=(1049481841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s5_1 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346714627/10000000000 : ℝ)*x 0 + (-1014084061/5000000000 : ℝ)*x 1 + (1311852301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346714627/10000000000 : ℝ)^4419 ≤ (8853247286047/20000000000000 : ℝ)^3395 := by
    have hnat : (5346714627 : ℕ)^4419*20000000000000^3395 ≤ 8853247286047^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346714627 10000000000 8853247286047 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014084061/5000000000 : ℝ)^4419 ≤ (6267330977621/50000000000000 : ℝ)^3395 := by
    have hnat : (1014084061 : ℕ)^4419*50000000000000^3395 ≤ 6267330977621^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014084061 5000000000 6267330977621 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311852301/2500000000 : ℝ)^4419 ≤ (1349971925211/3125000000000 : ℝ)^3395 := by
    have hnat : (1311852301 : ℕ)^4419*3125000000000^3395 ≤ 1349971925211^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311852301 2500000000 1349971925211 3125000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346714627/10000000000 : ℝ), (-1014084061/5000000000 : ℝ), (1311852301/2500000000 : ℝ)] ![(8853247286047/20000000000000 : ℝ), (6267330977621/50000000000000 : ℝ), (1349971925211/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346714627/10000000000 : ℝ)|^4419 ≤ (8853247286047/20000000000000 : ℝ)^3395
        have hw : |(5346714627/10000000000 : ℝ)|=(5346714627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1014084061/5000000000 : ℝ)|^4419 ≤ (6267330977621/50000000000000 : ℝ)^3395
        have hw : |(-1014084061/5000000000 : ℝ)|=(1014084061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311852301/2500000000 : ℝ)|^4419 ≤ (1349971925211/3125000000000 : ℝ)^3395
        have hw : |(1311852301/2500000000 : ℝ)|=(1311852301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s5_2 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42773717/80000000 : ℝ)*x 0 + (5247409207/10000000000 : ℝ)*x 1 + (-50704203/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42773717/80000000 : ℝ)^4419 ≤ (22133118204341/50000000000000 : ℝ)^3395 := by
    have hnat : (42773717 : ℕ)^4419*50000000000000^3395 ≤ 22133118204341^3395*80000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42773717 80000000 22133118204341 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247409207/10000000000 : ℝ)^4419 ≤ (21599550819449/50000000000000 : ℝ)^3395 := by
    have hnat : (5247409207 : ℕ)^4419*50000000000000^3395 ≤ 21599550819449^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247409207 10000000000 21599550819449 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50704203/250000000 : ℝ)^4419 ≤ (12534661939153/100000000000000 : ℝ)^3395 := by
    have hnat : (50704203 : ℕ)^4419*100000000000000^3395 ≤ 12534661939153^3395*250000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50704203 250000000 12534661939153 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42773717/80000000 : ℝ), (5247409207/10000000000 : ℝ), (-50704203/250000000 : ℝ)] ![(22133118204341/50000000000000 : ℝ), (21599550819449/50000000000000 : ℝ), (12534661939153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42773717/80000000 : ℝ)|^4419 ≤ (22133118204341/50000000000000 : ℝ)^3395
        have hw : |(42773717/80000000 : ℝ)|=(42773717/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247409207/10000000000 : ℝ)|^4419 ≤ (21599550819449/50000000000000 : ℝ)^3395
        have hw : |(5247409207/10000000000 : ℝ)|=(5247409207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50704203/250000000 : ℝ)|^4419 ≤ (12534661939153/100000000000000 : ℝ)^3395
        have hw : |(-50704203/250000000 : ℝ)|=(50704203/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s5_3 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53711487/125000000 : ℝ)*x 0 + (206287049/500000000 : ℝ)*x 1 + (178975043/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53711487/125000000 : ℝ)^4419 ≤ (8326261074633/25000000000000 : ℝ)^3395 := by
    have hnat : (53711487 : ℕ)^4419*25000000000000^3395 ≤ 8326261074633^3395*125000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53711487 125000000 8326261074633 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206287049/500000000 : ℝ)^4419 ≤ (3158854689353/10000000000000 : ℝ)^3395 := by
    have hnat : (206287049 : ℕ)^4419*10000000000000^3395 ≤ 3158854689353^3395*500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206287049 500000000 3158854689353 10000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178975043/400000000 : ℝ)^4419 ≤ (35106408797071/100000000000000 : ℝ)^3395 := by
    have hnat : (178975043 : ℕ)^4419*100000000000000^3395 ≤ 35106408797071^3395*400000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178975043 400000000 35106408797071 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53711487/125000000 : ℝ), (206287049/500000000 : ℝ), (178975043/400000000 : ℝ)] ![(8326261074633/25000000000000 : ℝ), (3158854689353/10000000000000 : ℝ), (35106408797071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53711487/125000000 : ℝ)|^4419 ≤ (8326261074633/25000000000000 : ℝ)^3395
        have hw : |(53711487/125000000 : ℝ)|=(53711487/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(206287049/500000000 : ℝ)|^4419 ≤ (3158854689353/10000000000000 : ℝ)^3395
        have hw : |(206287049/500000000 : ℝ)|=(206287049/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(178975043/400000000 : ℝ)|^4419 ≤ (35106408797071/100000000000000 : ℝ)^3395
        have hw : |(178975043/400000000 : ℝ)|=(178975043/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s5_4 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1947042517/10000000000 : ℝ)*x 0 + (2623993293/5000000000 : ℝ)*x 1 + (2703115693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1947042517/10000000000 : ℝ)^4419 ≤ (2971507574883/25000000000000 : ℝ)^3395 := by
    have hnat : (1947042517 : ℕ)^4419*25000000000000^3395 ≤ 2971507574883^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947042517 10000000000 2971507574883 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623993293/5000000000 : ℝ)^4419 ≤ (21602644334263/50000000000000 : ℝ)^3395 := by
    have hnat : (2623993293 : ℕ)^4419*50000000000000^3395 ≤ 21602644334263^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623993293 5000000000 21602644334263 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703115693/5000000000 : ℝ)^4419 ≤ (44908681008387/100000000000000 : ℝ)^3395 := by
    have hnat : (2703115693 : ℕ)^4419*100000000000000^3395 ≤ 44908681008387^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703115693 5000000000 44908681008387 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1947042517/10000000000 : ℝ), (2623993293/5000000000 : ℝ), (2703115693/5000000000 : ℝ)] ![(2971507574883/25000000000000 : ℝ), (21602644334263/50000000000000 : ℝ), (44908681008387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1947042517/10000000000 : ℝ)|^4419 ≤ (2971507574883/25000000000000 : ℝ)^3395
        have hw : |(-1947042517/10000000000 : ℝ)|=(1947042517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623993293/5000000000 : ℝ)|^4419 ≤ (21602644334263/50000000000000 : ℝ)^3395
        have hw : |(2623993293/5000000000 : ℝ)|=(2623993293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703115693/5000000000 : ℝ)|^4419 ≤ (44908681008387/100000000000000 : ℝ)^3395
        have hw : |(2703115693/5000000000 : ℝ)|=(2703115693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s5_5 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305155663/10000000000 : ℝ)*x 0 + (-1869345963/10000000000 : ℝ)*x 1 + (5406231429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305155663/10000000000 : ℝ)^4419 ≤ (8763782070089/20000000000000 : ℝ)^3395 := by
    have hnat : (5305155663 : ℕ)^4419*20000000000000^3395 ≤ 8763782070089^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305155663 10000000000 8763782070089 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1869345963/10000000000 : ℝ)^4419 ≤ (11272408158393/100000000000000 : ℝ)^3395 := by
    have hnat : (1869345963 : ℕ)^4419*100000000000000^3395 ≤ 11272408158393^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869345963 10000000000 11272408158393 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406231429/10000000000 : ℝ)^4419 ≤ (44908681473317/100000000000000 : ℝ)^3395 := by
    have hnat : (5406231429 : ℕ)^4419*100000000000000^3395 ≤ 44908681473317^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406231429 10000000000 44908681473317 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305155663/10000000000 : ℝ), (-1869345963/10000000000 : ℝ), (5406231429/10000000000 : ℝ)] ![(8763782070089/20000000000000 : ℝ), (11272408158393/100000000000000 : ℝ), (44908681473317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305155663/10000000000 : ℝ)|^4419 ≤ (8763782070089/20000000000000 : ℝ)^3395
        have hw : |(5305155663/10000000000 : ℝ)|=(5305155663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1869345963/10000000000 : ℝ)|^4419 ≤ (11272408158393/100000000000000 : ℝ)^3395
        have hw : |(-1869345963/10000000000 : ℝ)|=(1869345963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406231429/10000000000 : ℝ)|^4419 ≤ (44908681473317/100000000000000 : ℝ)^3395
        have hw : |(5406231429/10000000000 : ℝ)|=(5406231429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s5_6 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652577911/5000000000 : ℝ)*x 0 + (1081246257/2000000000 : ℝ)*x 1 + (-373869189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652577911/5000000000 : ℝ)^4419 ≤ (876378241197/2000000000000 : ℝ)^3395 := by
    have hnat : (2652577911 : ℕ)^4419*2000000000000^3395 ≤ 876378241197^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652577911 5000000000 876378241197 2000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081246257/2000000000 : ℝ)^4419 ≤ (2245433995817/5000000000000 : ℝ)^3395 := by
    have hnat : (1081246257 : ℕ)^4419*5000000000000^3395 ≤ 2245433995817^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081246257 2000000000 2245433995817 5000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373869189/2000000000 : ℝ)^4419 ≤ (1409051002139/12500000000000 : ℝ)^3395 := by
    have hnat : (373869189 : ℕ)^4419*12500000000000^3395 ≤ 1409051002139^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373869189 2000000000 1409051002139 12500000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652577911/5000000000 : ℝ), (1081246257/2000000000 : ℝ), (-373869189/2000000000 : ℝ)] ![(876378241197/2000000000000 : ℝ), (2245433995817/5000000000000 : ℝ), (1409051002139/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652577911/5000000000 : ℝ)|^4419 ≤ (876378241197/2000000000000 : ℝ)^3395
        have hw : |(2652577911/5000000000 : ℝ)|=(2652577911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081246257/2000000000 : ℝ)|^4419 ≤ (2245433995817/5000000000000 : ℝ)^3395
        have hw : |(1081246257/2000000000 : ℝ)|=(1081246257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-373869189/2000000000 : ℝ)|^4419 ≤ (1409051002139/12500000000000 : ℝ)^3395
        have hw : |(-373869189/2000000000 : ℝ)|=(373869189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s5_7 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4296943283/10000000000 : ℝ)*x 0 + (4473113071/10000000000 : ℝ)*x 1 + (412701053/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296943283/10000000000 : ℝ)^4419 ≤ (33305289687247/100000000000000 : ℝ)^3395 := by
    have hnat : (4296943283 : ℕ)^4419*100000000000000^3395 ≤ 33305289687247^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296943283 10000000000 33305289687247 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4473113071/10000000000 : ℝ)^4419 ≤ (35093510737423/100000000000000 : ℝ)^3395 := by
    have hnat : (4473113071 : ℕ)^4419*100000000000000^3395 ≤ 35093510737423^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473113071 10000000000 35093510737423 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412701053/1000000000 : ℝ)^4419 ≤ (31601199554593/100000000000000 : ℝ)^3395 := by
    have hnat : (412701053 : ℕ)^4419*100000000000000^3395 ≤ 31601199554593^3395*1000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412701053 1000000000 31601199554593 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296943283/10000000000 : ℝ), (4473113071/10000000000 : ℝ), (412701053/1000000000 : ℝ)] ![(33305289687247/100000000000000 : ℝ), (35093510737423/100000000000000 : ℝ), (31601199554593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296943283/10000000000 : ℝ)|^4419 ≤ (33305289687247/100000000000000 : ℝ)^3395
        have hw : |(4296943283/10000000000 : ℝ)|=(4296943283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4473113071/10000000000 : ℝ)|^4419 ≤ (35093510737423/100000000000000 : ℝ)^3395
        have hw : |(4473113071/10000000000 : ℝ)|=(4473113071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(412701053/1000000000 : ℝ)|^4419 ≤ (31601199554593/100000000000000 : ℝ)^3395
        have hw : |(412701053/1000000000 : ℝ)|=(412701053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1459_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11397/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (591/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2959/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5689/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2959/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5689/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2959/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5689/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2959/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5689/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2959/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5689/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2959/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5689/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5689/50000 : ℝ) ^ (2209/512 : ℝ) ≤ (528835640934509/6250000000000000000 : ℝ) := by
    have hpowers : (5689/50000 : ℝ)^2209 ≤ (528835640934509/6250000000000000000 : ℝ)^512 := by
      have hnat : (5689 : ℕ)^2209*6250000000000000000^512 ≤ 528835640934509^512*50000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5689 50000 528835640934509 6250000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5689/50000 : ℝ)) (X := (528835640934509/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2959/20000 : ℝ) ^ (2209/512 : ℝ) ≤ (2627241143866211/10000000000000000000 : ℝ) := by
    have hpowers : (2959/20000 : ℝ)^2209 ≤ (2627241143866211/10000000000000000000 : ℝ)^512 := by
      have hnat : (2959 : ℕ)^2209*10000000000000000000^512 ≤ 2627241143866211^512*20000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2959 20000 2627241143866211 10000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2959/20000 : ℝ)) (X := (2627241143866211/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125528835640934509/3125000000000000000 : ℝ) ≤ (5000196104119307/5000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (3125528835640934509/3125000000000000000 : ℝ)^512 ≤ (5000196104119307/5000000000000000 : ℝ)^2209 := by
      have hnat : (3125528835640934509 : ℕ)^512*5000000000000000^2209 ≤ 5000196104119307^2209*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125528835640934509 3125000000000000000 5000196104119307 5000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000196104119307/5000000000000000 : ℝ)) (X := (3125528835640934509/3125000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017366890846807127/50000000000000000000 : ℝ) ≤ (5000402474515201/5000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (50017366890846807127/50000000000000000000 : ℝ)^512 ≤ (5000402474515201/5000000000000000 : ℝ)^2209 := by
      have hnat : (50017366890846807127 : ℕ)^512*5000000000000000^2209 ≤ 5000402474515201^2209*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017366890846807127 50000000000000000000 5000402474515201 5000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000402474515201/5000000000000000 : ℝ)) (X := (50017366890846807127/50000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002627241143866211/5000000000000000000 : ℝ) ≤ (1000121768982219/1000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (5002627241143866211/5000000000000000000 : ℝ)^512 ≤ (1000121768982219/1000000000000000 : ℝ)^2209 := by
      have hnat : (5002627241143866211 : ℕ)^512*1000000000000000^2209 ≤ 1000121768982219^2209*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002627241143866211 5000000000000000000 1000121768982219 1000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000121768982219/1000000000000000 : ℝ)) (X := (5002627241143866211/5000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(528835640934509/6250000000000000000 : ℝ) ≤ ((3416194784609341631/3417000000000000000 : ℝ)+2*(103185197947/85425000000000 : ℝ)*(5689/50000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (3416194784609341631/3417000000000000000 : ℝ)+2*(103185197947/85425000000000 : ℝ)*(5689/50000 : ℝ)=(5000196104119307/5000000000000000 : ℝ) by norm_num, show 1+2*(528835640934509/6250000000000000000 : ℝ)=(3125528835640934509/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2627241143866211/10000000000000000000 : ℝ)+(528835640934509/6250000000000000000 : ℝ) ≤ ((3416194784609341631/3417000000000000000 : ℝ)+(103185197947/85425000000000 : ℝ)*((2959/20000 : ℝ)+(5689/50000 : ℝ)))^(2209/512 : ℝ) := by
    rw [show (3416194784609341631/3417000000000000000 : ℝ)+(103185197947/85425000000000 : ℝ)*((2959/20000 : ℝ)+(5689/50000 : ℝ))=(5000402474515201/5000000000000000 : ℝ) by norm_num, show 1+(2627241143866211/10000000000000000000 : ℝ)+(528835640934509/6250000000000000000 : ℝ)=(50017366890846807127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2627241143866211/10000000000000000000 : ℝ) ≤ ((3416194784609341631/3417000000000000000 : ℝ)+2*(103185197947/85425000000000 : ℝ)*(2959/20000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (3416194784609341631/3417000000000000000 : ℝ)+2*(103185197947/85425000000000 : ℝ)*(2959/20000 : ℝ)=(1000121768982219/1000000000000000 : ℝ) by norm_num, show 1+2*(2627241143866211/10000000000000000000 : ℝ)=(5002627241143866211/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3416194784609341631/3417000000000000000 : ℝ)*(X 1 0+X 2 0)+(103185197947/85425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (3416194784609341631/3417000000000000000 : ℝ)) (alpha := (103185197947/85425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3416194784609341631/3417000000000000000 : ℝ)*(X 0 1+X 2 1)+(103185197947/85425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (3416194784609341631/3417000000000000000 : ℝ)) (alpha := (103185197947/85425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3416194784609341631/3417000000000000000 : ℝ)*(X 0 2+X 1 2)+(103185197947/85425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (3416194784609341631/3417000000000000000 : ℝ)) (alpha := (103185197947/85425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-38940627/200000000 : ℝ)*X 0 0+(1081362361/2000000000 : ℝ)*X 0 1+(1049481841/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346714627/10000000000 : ℝ)*X 1 0+(-1014084061/5000000000 : ℝ)*X 1 1+(1311852301/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42773717/80000000 : ℝ)*X 2 0+(5247409207/10000000000 : ℝ)*X 2 1+(-50704203/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((53711487/125000000 : ℝ)*X 0 0+(206287049/500000000 : ℝ)*X 0 1+(178975043/400000000 : ℝ)*X 0 2+(53711487/125000000 : ℝ)*X 1 0+(206287049/500000000 : ℝ)*X 1 1+(178975043/400000000 : ℝ)*X 1 2+(53711487/125000000 : ℝ)*X 2 0+(206287049/500000000 : ℝ)*X 2 1+(178975043/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1947042517/10000000000 : ℝ)*X 0 0+(2623993293/5000000000 : ℝ)*X 0 1+(2703115693/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305155663/10000000000 : ℝ)*X 1 0+(-1869345963/10000000000 : ℝ)*X 1 1+(5406231429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652577911/5000000000 : ℝ)*X 2 0+(1081246257/2000000000 : ℝ)*X 2 1+(-373869189/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4296943283/10000000000 : ℝ)*X 0 0+(4473113071/10000000000 : ℝ)*X 0 1+(412701053/1000000000 : ℝ)*X 0 2+(4296943283/10000000000 : ℝ)*X 1 0+(4473113071/10000000000 : ℝ)*X 1 1+(412701053/1000000000 : ℝ)*X 1 2+(4296943283/10000000000 : ℝ)*X 2 0+(4473113071/10000000000 : ℝ)*X 2 1+(412701053/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (277104394204192675952482111/28475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1738441507/100000000000000 : ℝ)*(base19) + (323710939/20000000000000 : ℝ)*(base23) + (62845357/100000000000000 : ℝ)*(lower2) + (239329293/100000000000000 : ℝ)*(upper3) + (77997453/50000000000000 : ℝ)*(upper5) + (2285465562874919/50000000000000 : ℝ)*(major0) + (2285465562874919/50000000000000 : ℝ)*(major1) + (2285465562874919/50000000000000 : ℝ)*(major2) + (6273461810619597/100000000000000 : ℝ)*(sp0) + (1568374246186747/25000000000000 : ℝ)*(sp1) + (31367485523169/500000000000 : ℝ)*(sp2) + (179271559451879/6250000000000 : ℝ)*(sp3) + (36912568899/100000000000000 : ℝ)*(sp4) + (71299601/390625000000 : ℝ)*(sp7) + (35854540049099/1250000000000 : ℝ)*(f.failure) + (1254699744637699/20000000000000 : ℝ)*(f.sum) + (20562282549169/17085000000000000000000000000 : ℝ)*base65 + (17172457761140963/56950000000000000000000000000000 : ℝ)*base67 + (869554246977659037/56950000000000000000000000000000 : ℝ)*base70 + (50933655341590963/56950000000000000000000000000000 : ℝ)*base71 + (1421156030371/266953125000000000000000000 : ℝ)*base73 + (683470934458990963/56950000000000000000000000000000 : ℝ)*base75 + (353156864950209037/56950000000000000000000000000000 : ℝ)*base78 + (797007874564190963/56950000000000000000000000000000 : ℝ)*base79 + (8973230222557/2135625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (105603/15625000000000000000 : ℝ)*base89 + (105603/15625000000000000000 : ℝ)*base91 + (105603/15625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (551251468617194546641712459/56950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (415217701/25000000000000 : ℝ)*(base19) + (1919133803/100000000000000 : ℝ)*(base23) + (22541453/12500000000000 : ℝ)*(upper3) + (33395557/100000000000000 : ℝ)*(lower4) + (125077599/50000000000000 : ℝ)*(upper5) + (4604321603861611/100000000000000 : ℝ)*(major0) + (4604321603861611/100000000000000 : ℝ)*(major1) + (4604321603861611/100000000000000 : ℝ)*(major2) + (38395576533/100000000000000 : ℝ)*(sp1) + (39151215109/100000000000000 : ℝ)*(sp2) + (631932639697779/10000000000000 : ℝ)*(sp4) + (6319286340530453/100000000000000 : ℝ)*(sp5) + (6319285326628879/100000000000000 : ℝ)*(sp6) + (1444658244046557/50000000000000 : ℝ)*(sp7) + (1444658244046557/50000000000000 : ℝ)*(f.failure) + (631932639697779/10000000000000 : ℝ)*(f.sum) + (254236215187/4271250000000000000000000000 : ℝ)*base65 + (882646641410635847/113900000000000000000000000000000 : ℝ)*base67 + (1451623917179235847/113900000000000000000000000000000 : ℝ)*base69 + (122205961874435847/113900000000000000000000000000000 : ℝ)*base71 + (2679309412997/17085000000000000000000000000 : ℝ)*base74 + (1468948092486135847/113900000000000000000000000000000 : ℝ)*base75 + (860238389374264153/113900000000000000000000000000000 : ℝ)*base78 + (777840310007564153/113900000000000000000000000000000 : ℝ)*base80 + (102883457932243/17085000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4072471/625000000000000000000 : ℝ)*base90 + (4072471/625000000000000000000 : ℝ)*base92 + (4072471/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1459_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (591/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1459_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1459_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (491/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (591/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1459_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1459_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1459_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (491/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (591/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1459_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
