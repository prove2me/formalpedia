-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1585_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:31:26.909991+00:00
-- url     : https://prove2.me/submissions/870b1dad-a61d-46a5-ae6a-31e427139f3f

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
theorem support_rectangle_w1585_s3_0 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-882557733/5000000000 : ℝ)*x 0 + (5425298319/10000000000 : ℝ)*x 1 + (2609638587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882557733/5000000000 : ℝ)^4667 ≤ (5420268850079/50000000000000 : ℝ)^3643 := by
    have hnat : (882557733 : ℕ)^4667*50000000000000^3643 ≤ 5420268850079^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882557733 5000000000 5420268850079 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425298319/10000000000 : ℝ)^4667 ≤ (45684991911563/100000000000000 : ℝ)^3643 := by
    have hnat : (5425298319 : ℕ)^4667*100000000000000^3643 ≤ 45684991911563^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425298319 10000000000 45684991911563 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609638587/5000000000 : ℝ)^4667 ≤ (869489407639/2000000000000 : ℝ)^3643 := by
    have hnat : (2609638587 : ℕ)^4667*2000000000000^3643 ≤ 869489407639^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609638587 5000000000 869489407639 2000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-882557733/5000000000 : ℝ), (5425298319/10000000000 : ℝ), (2609638587/5000000000 : ℝ)] ![(5420268850079/50000000000000 : ℝ), (45684991911563/100000000000000 : ℝ), (869489407639/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-882557733/5000000000 : ℝ)|^4667 ≤ (5420268850079/50000000000000 : ℝ)^3643
        have hw : |(-882557733/5000000000 : ℝ)|=(882557733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425298319/10000000000 : ℝ)|^4667 ≤ (45684991911563/100000000000000 : ℝ)^3643
        have hw : |(5425298319/10000000000 : ℝ)|=(5425298319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609638587/5000000000 : ℝ)|^4667 ≤ (869489407639/2000000000000 : ℝ)^3643
        have hw : |(2609638587/5000000000 : ℝ)|=(2609638587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s3_1 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347633181/10000000000 : ℝ)*x 0 + (-3653351/19531250 : ℝ)*x 1 + (5219277169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347633181/10000000000 : ℝ)^4667 ≤ (44848855755681/100000000000000 : ℝ)^3643 := by
    have hnat : (5347633181 : ℕ)^4667*100000000000000^3643 ≤ 44848855755681^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347633181 10000000000 44848855755681 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3653351/19531250 : ℝ)^4667 ≤ (5838336951037/50000000000000 : ℝ)^3643 := by
    have hnat : (3653351 : ℕ)^4667*50000000000000^3643 ≤ 5838336951037^3643*19531250^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3653351 19531250 5838336951037 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219277169/10000000000 : ℝ)^4667 ≤ (10868617582149/25000000000000 : ℝ)^3643 := by
    have hnat : (5219277169 : ℕ)^4667*25000000000000^3643 ≤ 10868617582149^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219277169 10000000000 10868617582149 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347633181/10000000000 : ℝ), (-3653351/19531250 : ℝ), (5219277169/10000000000 : ℝ)] ![(44848855755681/100000000000000 : ℝ), (5838336951037/50000000000000 : ℝ), (10868617582149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347633181/10000000000 : ℝ)|^4667 ≤ (44848855755681/100000000000000 : ℝ)^3643
        have hw : |(5347633181/10000000000 : ℝ)|=(5347633181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3653351/19531250 : ℝ)|^4667 ≤ (5838336951037/50000000000000 : ℝ)^3643
        have hw : |(-3653351/19531250 : ℝ)|=(3653351/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219277169/10000000000 : ℝ)|^4667 ≤ (10868617582149/25000000000000 : ℝ)^3643
        have hw : |(5219277169/10000000000 : ℝ)|=(5219277169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s3_2 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336908289/2500000000 : ℝ)*x 0 + (326204823/625000000 : ℝ)*x 1 + (-1870515747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336908289/2500000000 : ℝ)^4667 ≤ (1121221387177/2500000000000 : ℝ)^3643 := by
    have hnat : (1336908289 : ℕ)^4667*2500000000000^3643 ≤ 1121221387177^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336908289 2500000000 1121221387177 2500000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326204823/625000000 : ℝ)^4667 ≤ (1738978812717/4000000000000 : ℝ)^3643 := by
    have hnat : (326204823 : ℕ)^4667*4000000000000^3643 ≤ 1738978812717^3643*625000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326204823 625000000 1738978812717 4000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870515747/10000000000 : ℝ)^4667 ≤ (467066967279/4000000000000 : ℝ)^3643 := by
    have hnat : (1870515747 : ℕ)^4667*4000000000000^3643 ≤ 467066967279^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870515747 10000000000 467066967279 4000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336908289/2500000000 : ℝ), (326204823/625000000 : ℝ), (-1870515747/10000000000 : ℝ)] ![(1121221387177/2500000000000 : ℝ), (1738978812717/4000000000000 : ℝ), (467066967279/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336908289/2500000000 : ℝ)|^4667 ≤ (1121221387177/2500000000000 : ℝ)^3643
        have hw : |(1336908289/2500000000 : ℝ)|=(1336908289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326204823/625000000 : ℝ)|^4667 ≤ (1738978812717/4000000000000 : ℝ)^3643
        have hw : |(326204823/625000000 : ℝ)|=(326204823/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1870515747/10000000000 : ℝ)|^4667 ≤ (467066967279/4000000000000 : ℝ)^3643
        have hw : |(-1870515747/10000000000 : ℝ)|=(1870515747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s3_3 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4236814997/10000000000 : ℝ)*x 0 + (159874567/400000000 : ℝ)*x 1 + (1122040811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4236814997/10000000000 : ℝ)^4667 ≤ (4160209101459/12500000000000 : ℝ)^3643 := by
    have hnat : (4236814997 : ℕ)^4667*12500000000000^3643 ≤ 4160209101459^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236814997 10000000000 4160209101459 12500000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159874567/400000000 : ℝ)^4667 ≤ (1544322098279/5000000000000 : ℝ)^3643 := by
    have hnat : (159874567 : ℕ)^4667*5000000000000^3643 ≤ 1544322098279^3643*400000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159874567 400000000 1544322098279 5000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122040811/2500000000 : ℝ)^4667 ≤ (17915942609551/50000000000000 : ℝ)^3643 := by
    have hnat : (1122040811 : ℕ)^4667*50000000000000^3643 ≤ 17915942609551^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122040811 2500000000 17915942609551 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4236814997/10000000000 : ℝ), (159874567/400000000 : ℝ), (1122040811/2500000000 : ℝ)] ![(4160209101459/12500000000000 : ℝ), (1544322098279/5000000000000 : ℝ), (17915942609551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4236814997/10000000000 : ℝ)|^4667 ≤ (4160209101459/12500000000000 : ℝ)^3643
        have hw : |(4236814997/10000000000 : ℝ)|=(4236814997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(159874567/400000000 : ℝ)|^4667 ≤ (1544322098279/5000000000000 : ℝ)^3643
        have hw : |(159874567/400000000 : ℝ)|=(159874567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122040811/2500000000 : ℝ)|^4667 ≤ (17915942609551/50000000000000 : ℝ)^3643
        have hw : |(1122040811/2500000000 : ℝ)|=(1122040811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s3_4 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1765142547/10000000000 : ℝ)*x 0 + (5220368023/10000000000 : ℝ)*x 1 + (2712099731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1765142547/10000000000 : ℝ)^4667 ≤ (1355093846249/12500000000000 : ℝ)^3643 := by
    have hnat : (1765142547 : ℕ)^4667*12500000000000^3643 ≤ 1355093846249^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765142547 10000000000 1355093846249 12500000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220368023/10000000000 : ℝ)^4667 ≤ (10871527776289/25000000000000 : ℝ)^3643 := by
    have hnat : (5220368023 : ℕ)^4667*25000000000000^3643 ≤ 10871527776289^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220368023 10000000000 10871527776289 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712099731/5000000000 : ℝ)^4667 ≤ (22836569058803/50000000000000 : ℝ)^3643 := by
    have hnat : (2712099731 : ℕ)^4667*50000000000000^3643 ≤ 22836569058803^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712099731 5000000000 22836569058803 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1765142547/10000000000 : ℝ), (5220368023/10000000000 : ℝ), (2712099731/5000000000 : ℝ)] ![(1355093846249/12500000000000 : ℝ), (10871527776289/25000000000000 : ℝ), (22836569058803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1765142547/10000000000 : ℝ)|^4667 ≤ (1355093846249/12500000000000 : ℝ)^3643
        have hw : |(-1765142547/10000000000 : ℝ)|=(1765142547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220368023/10000000000 : ℝ)|^4667 ≤ (10871527776289/25000000000000 : ℝ)^3643
        have hw : |(5220368023/10000000000 : ℝ)|=(5220368023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712099731/5000000000 : ℝ)|^4667 ≤ (22836569058803/50000000000000 : ℝ)^3643
        have hw : |(2712099731/5000000000 : ℝ)|=(2712099731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s3_5 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293030813/10000000000 : ℝ)*x 0 + (-1665593283/10000000000 : ℝ)*x 1 + (339012529/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293030813/10000000000 : ℝ)^4667 ≤ (44263048618581/100000000000000 : ℝ)^3643 := by
    have hnat : (5293030813 : ℕ)^4667*100000000000000^3643 ≤ 44263048618581^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293030813 10000000000 44263048618581 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1665593283/10000000000 : ℝ)^4667 ≤ (10063802438917/100000000000000 : ℝ)^3643 := by
    have hnat : (1665593283 : ℕ)^4667*100000000000000^3643 ≤ 10063802438917^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665593283 10000000000 10063802438917 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339012529/625000000 : ℝ)^4667 ≤ (22836574463129/50000000000000 : ℝ)^3643 := by
    have hnat : (339012529 : ℕ)^4667*50000000000000^3643 ≤ 22836574463129^3643*625000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339012529 625000000 22836574463129 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293030813/10000000000 : ℝ), (-1665593283/10000000000 : ℝ), (339012529/625000000 : ℝ)] ![(44263048618581/100000000000000 : ℝ), (10063802438917/100000000000000 : ℝ), (22836574463129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293030813/10000000000 : ℝ)|^4667 ≤ (44263048618581/100000000000000 : ℝ)^3643
        have hw : |(5293030813/10000000000 : ℝ)|=(5293030813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1665593283/10000000000 : ℝ)|^4667 ≤ (10063802438917/100000000000000 : ℝ)^3643
        have hw : |(-1665593283/10000000000 : ℝ)|=(1665593283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339012529/625000000 : ℝ)|^4667 ≤ (22836574463129/50000000000000 : ℝ)^3643
        have hw : |(339012529/625000000 : ℝ)|=(339012529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s3_6 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661628941/1250000000 : ℝ)*x 0 + (2712099627/5000000000 : ℝ)*x 1 + (-1665593979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661628941/1250000000 : ℝ)^4667 ≤ (22131528139227/50000000000000 : ℝ)^3643 := by
    have hnat : (661628941 : ℕ)^4667*50000000000000^3643 ≤ 22131528139227^3643*1250000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661628941 1250000000 22131528139227 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712099627/5000000000 : ℝ)^4667 ≤ (45673135873893/100000000000000 : ℝ)^3643 := by
    have hnat : (2712099627 : ℕ)^4667*100000000000000^3643 ≤ 45673135873893^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712099627 5000000000 45673135873893 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1665593979/10000000000 : ℝ)^4667 ≤ (10063807826339/100000000000000 : ℝ)^3643 := by
    have hnat : (1665593979 : ℕ)^4667*100000000000000^3643 ≤ 10063807826339^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665593979 10000000000 10063807826339 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661628941/1250000000 : ℝ), (2712099627/5000000000 : ℝ), (-1665593979/10000000000 : ℝ)] ![(22131528139227/50000000000000 : ℝ), (45673135873893/100000000000000 : ℝ), (10063807826339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661628941/1250000000 : ℝ)|^4667 ≤ (22131528139227/50000000000000 : ℝ)^3643
        have hw : |(661628941/1250000000 : ℝ)|=(661628941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712099627/5000000000 : ℝ)|^4667 ≤ (45673135873893/100000000000000 : ℝ)^3643
        have hw : |(2712099627/5000000000 : ℝ)|=(2712099627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1665593979/10000000000 : ℝ)|^4667 ≤ (10063807826339/100000000000000 : ℝ)^3643
        have hw : |(-1665593979/10000000000 : ℝ)|=(1665593979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s3_7 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118440291/5000000000 : ℝ)*x 0 + (2242781423/5000000000 : ℝ)*x 1 + (3999483579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118440291/5000000000 : ℝ)^4667 ≤ (33282332820499/100000000000000 : ℝ)^3643 := by
    have hnat : (2118440291 : ℕ)^4667*100000000000000^3643 ≤ 33282332820499^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118440291 5000000000 33282332820499 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242781423/5000000000 : ℝ)^4667 ≤ (35805291192689/100000000000000 : ℝ)^3643 := by
    have hnat : (2242781423 : ℕ)^4667*100000000000000^3643 ≤ 35805291192689^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242781423 5000000000 35805291192689 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3999483579/10000000000 : ℝ)^4667 ≤ (30912375971239/100000000000000 : ℝ)^3643 := by
    have hnat : (3999483579 : ℕ)^4667*100000000000000^3643 ≤ 30912375971239^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3999483579 10000000000 30912375971239 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118440291/5000000000 : ℝ), (2242781423/5000000000 : ℝ), (3999483579/10000000000 : ℝ)] ![(33282332820499/100000000000000 : ℝ), (35805291192689/100000000000000 : ℝ), (30912375971239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118440291/5000000000 : ℝ)|^4667 ≤ (33282332820499/100000000000000 : ℝ)^3643
        have hw : |(2118440291/5000000000 : ℝ)|=(2118440291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242781423/5000000000 : ℝ)|^4667 ≤ (35805291192689/100000000000000 : ℝ)^3643
        have hw : |(2242781423/5000000000 : ℝ)|=(2242781423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3999483579/10000000000 : ℝ)|^4667 ≤ (30912375971239/100000000000000 : ℝ)^3643
        have hw : |(3999483579/10000000000 : ℝ)|=(3999483579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1585_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7887/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5571/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15513/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7887/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7887/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7887/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7887/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7887/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7887/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10901/100000 : ℝ) ^ (4665/1024 : ℝ) ≤ (824232984342293/20000000000000000000 : ℝ) := by
    have hpowers : (10901/100000 : ℝ)^4665 ≤ (824232984342293/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10901 : ℕ)^4665*20000000000000000000^1024 ≤ 824232984342293^1024*100000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10901 100000 824232984342293 20000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10901/100000 : ℝ)) (X := (824232984342293/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7887/50000 : ℝ) ^ (4665/1024 : ℝ) ≤ (22186686585363381/100000000000000000000 : ℝ) := by
    have hpowers : (7887/50000 : ℝ)^4665 ≤ (22186686585363381/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7887 : ℕ)^4665*100000000000000000000^1024 ≤ 22186686585363381^1024*50000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7887 50000 22186686585363381 100000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7887/50000 : ℝ)) (X := (22186686585363381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000824232984342293/10000000000000000000 : ℝ) ≤ (10000180919063071/10000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (10000824232984342293/10000000000000000000 : ℝ)^1024 ≤ (10000180919063071/10000000000000000 : ℝ)^4665 := by
      have hnat : (10000824232984342293 : ℕ)^1024*10000000000000000^4665 ≤ 10000180919063071^4665*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000824232984342293 10000000000000000000 10000180919063071 10000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000180919063071/10000000000000000 : ℝ)) (X := (10000824232984342293/10000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013153925753537423/50000000000000000000 : ℝ) ≤ (2500144354097777/2500000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (50013153925753537423/50000000000000000000 : ℝ)^1024 ≤ (2500144354097777/2500000000000000 : ℝ)^4665 := by
      have hnat : (50013153925753537423 : ℕ)^1024*2500000000000000^4665 ≤ 2500144354097777^4665*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013153925753537423 50000000000000000000 2500144354097777 2500000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500144354097777/2500000000000000 : ℝ)) (X := (50013153925753537423/50000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022186686585363381/50000000000000000000 : ℝ) ≤ (2000194782743829/2000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (50022186686585363381/50000000000000000000 : ℝ)^1024 ≤ (2000194782743829/2000000000000000 : ℝ)^4665 := by
      have hnat : (50022186686585363381 : ℕ)^1024*2000000000000000^4665 ≤ 2000194782743829^4665*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022186686585363381 50000000000000000000 2000194782743829 2000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000194782743829/2000000000000000 : ℝ)) (X := (50022186686585363381/50000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(824232984342293/20000000000000000000 : ℝ) ≤ ((4429294289440771119/4430000000000000000 : ℝ)+2*(396497328037/487300000000000 : ℝ)*(10901/100000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (4429294289440771119/4430000000000000000 : ℝ)+2*(396497328037/487300000000000 : ℝ)*(10901/100000 : ℝ)=(10000180919063071/10000000000000000 : ℝ) by norm_num, show 1+2*(824232984342293/20000000000000000000 : ℝ)=(10000824232984342293/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22186686585363381/100000000000000000000 : ℝ)+(824232984342293/20000000000000000000 : ℝ) ≤ ((4429294289440771119/4430000000000000000 : ℝ)+(396497328037/487300000000000 : ℝ)*((7887/50000 : ℝ)+(10901/100000 : ℝ)))^(4665/1024 : ℝ) := by
    rw [show (4429294289440771119/4430000000000000000 : ℝ)+(396497328037/487300000000000 : ℝ)*((7887/50000 : ℝ)+(10901/100000 : ℝ))=(2500144354097777/2500000000000000 : ℝ) by norm_num, show 1+(22186686585363381/100000000000000000000 : ℝ)+(824232984342293/20000000000000000000 : ℝ)=(50013153925753537423/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22186686585363381/100000000000000000000 : ℝ) ≤ ((4429294289440771119/4430000000000000000 : ℝ)+2*(396497328037/487300000000000 : ℝ)*(7887/50000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (4429294289440771119/4430000000000000000 : ℝ)+2*(396497328037/487300000000000 : ℝ)*(7887/50000 : ℝ)=(2000194782743829/2000000000000000 : ℝ) by norm_num, show 1+2*(22186686585363381/100000000000000000000 : ℝ)=(50022186686585363381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4429294289440771119/4430000000000000000 : ℝ)*(X 1 0+X 2 0)+(396497328037/487300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (10901/100000 : ℝ)) (hi := (7887/50000 : ℝ)) (c := (4429294289440771119/4430000000000000000 : ℝ)) (alpha := (396497328037/487300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4429294289440771119/4430000000000000000 : ℝ)*(X 0 1+X 2 1)+(396497328037/487300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (10901/100000 : ℝ)) (hi := (7887/50000 : ℝ)) (c := (4429294289440771119/4430000000000000000 : ℝ)) (alpha := (396497328037/487300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4429294289440771119/4430000000000000000 : ℝ)*(X 0 2+X 1 2)+(396497328037/487300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (10901/100000 : ℝ)) (hi := (7887/50000 : ℝ)) (c := (4429294289440771119/4430000000000000000 : ℝ)) (alpha := (396497328037/487300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-882557733/5000000000 : ℝ)*X 0 0+(5425298319/10000000000 : ℝ)*X 0 1+(2609638587/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347633181/10000000000 : ℝ)*X 1 0+(-3653351/19531250 : ℝ)*X 1 1+(5219277169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336908289/2500000000 : ℝ)*X 2 0+(326204823/625000000 : ℝ)*X 2 1+(-1870515747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4236814997/10000000000 : ℝ)*X 0 0+(159874567/400000000 : ℝ)*X 0 1+(1122040811/2500000000 : ℝ)*X 0 2+(4236814997/10000000000 : ℝ)*X 1 0+(159874567/400000000 : ℝ)*X 1 1+(1122040811/2500000000 : ℝ)*X 1 2+(4236814997/10000000000 : ℝ)*X 2 0+(159874567/400000000 : ℝ)*X 2 1+(1122040811/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1765142547/10000000000 : ℝ)*X 0 0+(5220368023/10000000000 : ℝ)*X 0 1+(2712099731/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293030813/10000000000 : ℝ)*X 1 0+(-1665593283/10000000000 : ℝ)*X 1 1+(339012529/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661628941/1250000000 : ℝ)*X 2 0+(2712099627/5000000000 : ℝ)*X 2 1+(-1665593979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2118440291/5000000000 : ℝ)*X 0 0+(2242781423/5000000000 : ℝ)*X 0 1+(3999483579/10000000000 : ℝ)*X 0 2+(2118440291/5000000000 : ℝ)*X 1 0+(2242781423/5000000000 : ℝ)*X 1 1+(3999483579/10000000000 : ℝ)*X 1 2+(2118440291/5000000000 : ℝ)*X 2 0+(2242781423/5000000000 : ℝ)*X 2 1+(3999483579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5004289995074476793780431989/1218250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (748898269/100000000000000 : ℝ)*(base19) + (671483501/100000000000000 : ℝ)*(base23) + (14631921/50000000000000 : ℝ)*(lower2) + (7831501/6250000000000 : ℝ)*(upper3) + (1475353/3125000000000 : ℝ)*(upper5) + (3444662693979493/100000000000000 : ℝ)*(major0) + (3444662693979493/100000000000000 : ℝ)*(major1) + (3444662693979493/100000000000000 : ℝ)*(major2) + (4853883792758087/100000000000000 : ℝ)*(sp0) + (2426947141048789/50000000000000 : ℝ)*(sp1) + (2426947179756173/50000000000000 : ℝ)*(sp2) + (1017712327905591/50000000000000 : ℝ)*(sp3) + (11238237759/100000000000000 : ℝ)*(sp4) + (2782113151/50000000000000 : ℝ)*(sp7) + (407086044007497/20000000000000 : ℝ)*(f.failure) + (4853895030995847/100000000000000 : ℝ)*(f.sum) + (25320678240177/12182500000000000000000000000 : ℝ)*base66 + (42274641536247389337/4873000000000000000000000000000000 : ℝ)*base67 + (92606569579017389337/4873000000000000000000000000000000 : ℝ)*base69 + (25973563393315389337/4873000000000000000000000000000000 : ℝ)*base71 + (98010085897051/24365000000000000000000000000 : ℝ)*base73 + (44357403330460610663/4873000000000000000000000000000000 : ℝ)*base76 + (11021209464781389337/4873000000000000000000000000000000 : ℝ)*base77 + (64873764195833389337/4873000000000000000000000000000000 : ℝ)*base79 + (234689403115781/24365000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (83837/500000000000000000000 : ℝ)*base90 + (83837/500000000000000000000 : ℝ)*base92 + (83837/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1887471168421136946804011487/152281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80207629/20000000000000 : ℝ)*(base19) + (809938197/50000000000000 : ℝ)*(base23) + (52484389/12500000000000 : ℝ)*(upper3) + (284802447/100000000000000 : ℝ)*(lower4) + (90857873/100000000000000 : ℝ)*(upper5) + (217602597605969/6250000000000 : ℝ)*(major0) + (217602597605969/6250000000000 : ℝ)*(major1) + (217602597605969/6250000000000 : ℝ)*(major2) + (12454088979/100000000000000 : ℝ)*(sp1) + (887744237/6250000000000 : ℝ)*(sp2) + (4906001902336239/100000000000000 : ℝ)*(sp4) + (981197809441823/20000000000000 : ℝ)*(sp5) + (2452993039276027/50000000000000 : ℝ)*(sp6) + (2057280807900119/100000000000000 : ℝ)*(sp7) + (2057280807900119/100000000000000 : ℝ)*(f.failure) + (4906001902336239/100000000000000 : ℝ)*(f.sum) + (15244790534023/24365000000000000000000000000 : ℝ)*base65 + (1800396081154414921/304562500000000000000000000000000 : ℝ)*base67 + (71155642016664921/304562500000000000000000000000000 : ℝ)*base69 + (1649151019478602421/304562500000000000000000000000000 : ℝ)*base71 + (36400004982083/24365000000000000000000000000 : ℝ)*base73 + (1852740768698602421/304562500000000000000000000000000 : ℝ)*base75 + (1122622762022022579/304562500000000000000000000000000 : ℝ)*base78 + (1488932301037772579/304562500000000000000000000000000 : ℝ)*base80 + (12346961098367/24365000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (11155299/2500000000000000000000 : ℝ)*base90 + (11155299/2500000000000000000000 : ℝ)*base92 + (11155299/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1585_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7887/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5571/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15513/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1585_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1585_s4_0 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-882652293/5000000000 : ℝ)*x 0 + (5424023239/10000000000 : ℝ)*x 1 + (5220426683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882652293/5000000000 : ℝ)^4667 ≤ (10842025691253/100000000000000 : ℝ)^3643 := by
    have hnat : (882652293 : ℕ)^4667*100000000000000^3643 ≤ 10842025691253^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882652293 5000000000 10842025691253 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424023239/10000000000 : ℝ)^4667 ≤ (45671237194989/100000000000000 : ℝ)^3643 := by
    have hnat : (5424023239 : ℕ)^4667*100000000000000^3643 ≤ 45671237194989^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424023239 10000000000 45671237194989 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220426683/10000000000 : ℝ)^4667 ≤ (43486737100099/100000000000000 : ℝ)^3643 := by
    have hnat : (5220426683 : ℕ)^4667*100000000000000^3643 ≤ 43486737100099^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220426683 10000000000 43486737100099 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-882652293/5000000000 : ℝ), (5424023239/10000000000 : ℝ), (5220426683/10000000000 : ℝ)] ![(10842025691253/100000000000000 : ℝ), (45671237194989/100000000000000 : ℝ), (43486737100099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-882652293/5000000000 : ℝ)|^4667 ≤ (10842025691253/100000000000000 : ℝ)^3643
        have hw : |(-882652293/5000000000 : ℝ)|=(882652293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424023239/10000000000 : ℝ)|^4667 ≤ (45671237194989/100000000000000 : ℝ)^3643
        have hw : |(5424023239/10000000000 : ℝ)|=(5424023239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220426683/10000000000 : ℝ)|^4667 ≤ (43486737100099/100000000000000 : ℝ)^3643
        have hw : |(5220426683/10000000000 : ℝ)|=(5220426683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s4_1 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673647201/5000000000 : ℝ)*x 0 + (-116839793/625000000 : ℝ)*x 1 + (5220426823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673647201/5000000000 : ℝ)^4667 ≤ (44845215926501/100000000000000 : ℝ)^3643 := by
    have hnat : (2673647201 : ℕ)^4667*100000000000000^3643 ≤ 44845215926501^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673647201 5000000000 44845215926501 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116839793/625000000 : ℝ)^4667 ≤ (2917011365391/25000000000000 : ℝ)^3643 := by
    have hnat : (116839793 : ℕ)^4667*25000000000000^3643 ≤ 2917011365391^3643*625000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116839793 625000000 2917011365391 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220426823/10000000000 : ℝ)^4667 ≤ (21743369297061/50000000000000 : ℝ)^3643 := by
    have hnat : (5220426823 : ℕ)^4667*50000000000000^3643 ≤ 21743369297061^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220426823 10000000000 21743369297061 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673647201/5000000000 : ℝ), (-116839793/625000000 : ℝ), (5220426823/10000000000 : ℝ)] ![(44845215926501/100000000000000 : ℝ), (2917011365391/25000000000000 : ℝ), (21743369297061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673647201/5000000000 : ℝ)|^4667 ≤ (44845215926501/100000000000000 : ℝ)^3643
        have hw : |(2673647201/5000000000 : ℝ)|=(2673647201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-116839793/625000000 : ℝ)|^4667 ≤ (2917011365391/25000000000000 : ℝ)^3643
        have hw : |(-116839793/625000000 : ℝ)|=(116839793/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220426823/10000000000 : ℝ)|^4667 ≤ (21743369297061/50000000000000 : ℝ)^3643
        have hw : |(5220426823/10000000000 : ℝ)|=(5220426823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s4_2 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347294631/10000000000 : ℝ)*x 0 + (2610213293/5000000000 : ℝ)*x 1 + (-1869436697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347294631/10000000000 : ℝ)^4667 ≤ (44845218386847/100000000000000 : ℝ)^3643 := by
    have hnat : (5347294631 : ℕ)^4667*100000000000000^3643 ≤ 44845218386847^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347294631 10000000000 44845218386847 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610213293/5000000000 : ℝ)^4667 ≤ (21743368032477/50000000000000 : ℝ)^3643 := by
    have hnat : (2610213293 : ℕ)^4667*50000000000000^3643 ≤ 21743368032477^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610213293 5000000000 21743368032477 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1869436697/10000000000 : ℝ)^4667 ≤ (11668045533527/100000000000000 : ℝ)^3643 := by
    have hnat : (1869436697 : ℕ)^4667*100000000000000^3643 ≤ 11668045533527^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869436697 10000000000 11668045533527 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347294631/10000000000 : ℝ), (2610213293/5000000000 : ℝ), (-1869436697/10000000000 : ℝ)] ![(44845218386847/100000000000000 : ℝ), (21743368032477/50000000000000 : ℝ), (11668045533527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347294631/10000000000 : ℝ)|^4667 ≤ (44845218386847/100000000000000 : ℝ)^3643
        have hw : |(5347294631/10000000000 : ℝ)|=(5347294631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610213293/5000000000 : ℝ)|^4667 ≤ (21743368032477/50000000000000 : ℝ)^3643
        have hw : |(2610213293/5000000000 : ℝ)|=(2610213293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1869436697/10000000000 : ℝ)|^4667 ≤ (11668045533527/100000000000000 : ℝ)^3643
        have hw : |(-1869436697/10000000000 : ℝ)|=(1869436697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s4_3 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059233791/2500000000 : ℝ)*x 0 + (999935591/2500000000 : ℝ)*x 1 + (560657319/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059233791/2500000000 : ℝ)^4667 ≤ (33282882103801/100000000000000 : ℝ)^3643 := by
    have hnat : (1059233791 : ℕ)^4667*100000000000000^3643 ≤ 33282882103801^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059233791 2500000000 33282882103801 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999935591/2500000000 : ℝ)^4667 ≤ (3864367298781/12500000000000 : ℝ)^3643 := by
    have hnat : (999935591 : ℕ)^4667*12500000000000^3643 ≤ 3864367298781^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999935591 2500000000 3864367298781 12500000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560657319/1250000000 : ℝ)^4667 ≤ (35802179489663/100000000000000 : ℝ)^3643 := by
    have hnat : (560657319 : ℕ)^4667*100000000000000^3643 ≤ 35802179489663^3643*1250000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560657319 1250000000 35802179489663 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059233791/2500000000 : ℝ), (999935591/2500000000 : ℝ), (560657319/1250000000 : ℝ)] ![(33282882103801/100000000000000 : ℝ), (3864367298781/12500000000000 : ℝ), (35802179489663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059233791/2500000000 : ℝ)|^4667 ≤ (33282882103801/100000000000000 : ℝ)^3643
        have hw : |(1059233791/2500000000 : ℝ)|=(1059233791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999935591/2500000000 : ℝ)|^4667 ≤ (3864367298781/12500000000000 : ℝ)^3643
        have hw : |(999935591/2500000000 : ℝ)|=(999935591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560657319/1250000000 : ℝ)|^4667 ≤ (35802179489663/100000000000000 : ℝ)^3643
        have hw : |(560657319/1250000000 : ℝ)|=(560657319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s4_4 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-441332757/2500000000 : ℝ)*x 0 + (5221491743/10000000000 : ℝ)*x 1 + (338934389/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441332757/2500000000 : ℝ)^4667 ≤ (2710558434943/25000000000000 : ℝ)^3643 := by
    have hnat : (441332757 : ℕ)^4667*25000000000000^3643 ≤ 2710558434943^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441332757 2500000000 2710558434943 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221491743/10000000000 : ℝ)^4667 ≤ (4349810331801/10000000000000 : ℝ)^3643 := by
    have hnat : (5221491743 : ℕ)^4667*10000000000000^3643 ≤ 4349810331801^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221491743 10000000000 4349810331801 10000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338934389/625000000 : ℝ)^4667 ≤ (4565966292571/10000000000000 : ℝ)^3643 := by
    have hnat : (338934389 : ℕ)^4667*10000000000000^3643 ≤ 4565966292571^3643*625000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338934389 625000000 4565966292571 10000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441332757/2500000000 : ℝ), (5221491743/10000000000 : ℝ), (338934389/625000000 : ℝ)] ![(2710558434943/25000000000000 : ℝ), (4349810331801/10000000000000 : ℝ), (4565966292571/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441332757/2500000000 : ℝ)|^4667 ≤ (2710558434943/25000000000000 : ℝ)^3643
        have hw : |(-441332757/2500000000 : ℝ)|=(441332757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221491743/10000000000 : ℝ)|^4667 ≤ (4349810331801/10000000000000 : ℝ)^3643
        have hw : |(5221491743/10000000000 : ℝ)|=(5221491743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338934389/625000000 : ℝ)|^4667 ≤ (4565966292571/10000000000000 : ℝ)^3643
        have hw : |(338934389/625000000 : ℝ)|=(338934389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s4_5 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293336419/10000000000 : ℝ)*x 0 + (-833456423/5000000000 : ℝ)*x 1 + (5422949919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293336419/10000000000 : ℝ)^4667 ≤ (22133161317793/50000000000000 : ℝ)^3643 := by
    have hnat : (5293336419 : ℕ)^4667*50000000000000^3643 ≤ 22133161317793^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293336419 10000000000 22133161317793 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833456423/5000000000 : ℝ)^4667 ≤ (1007401771823/10000000000000 : ℝ)^3643 := by
    have hnat : (833456423 : ℕ)^4667*10000000000000^3643 ≤ 1007401771823^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833456423 5000000000 1007401771823 10000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422949919/10000000000 : ℝ)^4667 ≤ (9131931927173/20000000000000 : ℝ)^3643 := by
    have hnat : (5422949919 : ℕ)^4667*20000000000000^3643 ≤ 9131931927173^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422949919 10000000000 9131931927173 20000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293336419/10000000000 : ℝ), (-833456423/5000000000 : ℝ), (5422949919/10000000000 : ℝ)] ![(22133161317793/50000000000000 : ℝ), (1007401771823/10000000000000 : ℝ), (9131931927173/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293336419/10000000000 : ℝ)|^4667 ≤ (22133161317793/50000000000000 : ℝ)^3643
        have hw : |(5293336419/10000000000 : ℝ)|=(5293336419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-833456423/5000000000 : ℝ)|^4667 ≤ (1007401771823/10000000000000 : ℝ)^3643
        have hw : |(-833456423/5000000000 : ℝ)|=(833456423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422949919/10000000000 : ℝ)|^4667 ≤ (9131931927173/20000000000000 : ℝ)^3643
        have hw : |(5422949919/10000000000 : ℝ)|=(5422949919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s4_6 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293335829/10000000000 : ℝ)*x 0 + (5422950287/10000000000 : ℝ)*x 1 + (-1666913149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293335829/10000000000 : ℝ)^4667 ≤ (44266316314749/100000000000000 : ℝ)^3643 := by
    have hnat : (5293335829 : ℕ)^4667*100000000000000^3643 ≤ 44266316314749^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293335829 10000000000 44266316314749 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422950287/10000000000 : ℝ)^4667 ≤ (11414915901313/25000000000000 : ℝ)^3643 := by
    have hnat : (5422950287 : ℕ)^4667*25000000000000^3643 ≤ 11414915901313^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422950287 10000000000 11414915901313 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1666913149/10000000000 : ℝ)^4667 ≤ (5037010032069/50000000000000 : ℝ)^3643 := by
    have hnat : (1666913149 : ℕ)^4667*50000000000000^3643 ≤ 5037010032069^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1666913149 10000000000 5037010032069 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293335829/10000000000 : ℝ), (5422950287/10000000000 : ℝ), (-1666913149/10000000000 : ℝ)] ![(44266316314749/100000000000000 : ℝ), (11414915901313/25000000000000 : ℝ), (5037010032069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293335829/10000000000 : ℝ)|^4667 ≤ (44266316314749/100000000000000 : ℝ)^3643
        have hw : |(5293335829/10000000000 : ℝ)|=(5293335829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422950287/10000000000 : ℝ)|^4667 ≤ (11414915901313/25000000000000 : ℝ)^3643
        have hw : |(5422950287/10000000000 : ℝ)|=(5422950287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1666913149/10000000000 : ℝ)|^4667 ≤ (5037010032069/50000000000000 : ℝ)^3643
        have hw : |(-1666913149/10000000000 : ℝ)|=(1666913149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s4_7 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4236997773/10000000000 : ℝ)*x 0 + (179308763/400000000 : ℝ)*x 1 + (4002300881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4236997773/10000000000 : ℝ)^4667 ≤ (8320878042219/25000000000000 : ℝ)^3643 := by
    have hnat : (4236997773 : ℕ)^4667*25000000000000^3643 ≤ 8320878042219^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236997773 10000000000 8320878042219 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179308763/400000000 : ℝ)^4667 ≤ (35776213174041/100000000000000 : ℝ)^3643 := by
    have hnat : (179308763 : ℕ)^4667*100000000000000^3643 ≤ 35776213174041^3643*400000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179308763 400000000 35776213174041 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4002300881/10000000000 : ℝ)^4667 ≤ (61880549281/200000000000 : ℝ)^3643 := by
    have hnat : (4002300881 : ℕ)^4667*200000000000^3643 ≤ 61880549281^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002300881 10000000000 61880549281 200000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4236997773/10000000000 : ℝ), (179308763/400000000 : ℝ), (4002300881/10000000000 : ℝ)] ![(8320878042219/25000000000000 : ℝ), (35776213174041/100000000000000 : ℝ), (61880549281/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4236997773/10000000000 : ℝ)|^4667 ≤ (8320878042219/25000000000000 : ℝ)^3643
        have hw : |(4236997773/10000000000 : ℝ)|=(4236997773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179308763/400000000 : ℝ)|^4667 ≤ (35776213174041/100000000000000 : ℝ)^3643
        have hw : |(179308763/400000000 : ℝ)|=(179308763/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4002300881/10000000000 : ℝ)|^4667 ≤ (61880549281/200000000000 : ℝ)^3643
        have hw : |(4002300881/10000000000 : ℝ)|=(4002300881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1585_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15513/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5583/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7743/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15513/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5571/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15513/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5571/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15513/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5571/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15513/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5571/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15513/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5571/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15513/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5571/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5571/50000 : ℝ) ^ (4665/1024 : ℝ) ≤ (4552859947594703/100000000000000000000 : ℝ) := by
    have hpowers : (5571/50000 : ℝ)^4665 ≤ (4552859947594703/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5571 : ℕ)^4665*100000000000000000000^1024 ≤ 4552859947594703^1024*50000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5571 50000 4552859947594703 100000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5571/50000 : ℝ)) (X := (4552859947594703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15513/100000 : ℝ) ^ (4665/1024 : ℝ) ≤ (10281391826989581/50000000000000000000 : ℝ) := by
    have hpowers : (15513/100000 : ℝ)^4665 ≤ (10281391826989581/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15513 : ℕ)^4665*50000000000000000000^1024 ≤ 10281391826989581^1024*100000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15513 100000 10281391826989581 50000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15513/100000 : ℝ)) (X := (10281391826989581/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004552859947594703/50000000000000000000 : ℝ) ≤ (1250024983724157/1250000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (50004552859947594703/50000000000000000000 : ℝ)^1024 ≤ (1250024983724157/1250000000000000 : ℝ)^4665 := by
      have hnat : (50004552859947594703 : ℕ)^1024*1250000000000000^4665 ≤ 1250024983724157^4665*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004552859947594703 50000000000000000000 1250024983724157 1250000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250024983724157/1250000000000000 : ℝ)) (X := (50004552859947594703/50000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005023128720314773/20000000000000000000 : ℝ) ≤ (2500137812961877/2500000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (20005023128720314773/20000000000000000000 : ℝ)^1024 ≤ (2500137812961877/2500000000000000 : ℝ)^4665 := by
      have hnat : (20005023128720314773 : ℕ)^1024*2500000000000000^4665 ≤ 2500137812961877^4665*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005023128720314773 20000000000000000000 2500137812961877 2500000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500137812961877/2500000000000000 : ℝ)) (X := (20005023128720314773/20000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010281391826989581/25000000000000000000 : ℝ) ≤ (31252820730943/31250000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (25010281391826989581/25000000000000000000 : ℝ)^1024 ≤ (31252820730943/31250000000000 : ℝ)^4665 := by
      have hnat : (25010281391826989581 : ℕ)^1024*31250000000000^4665 ≤ 31252820730943^4665*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010281391826989581 25000000000000000000 31252820730943 31250000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31252820730943/31250000000000 : ℝ)) (X := (25010281391826989581/25000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4552859947594703/100000000000000000000 : ℝ) ≤ ((1820960143048723767/1821250000000000000 : ℝ)+2*(87845513563/109275000000000 : ℝ)*(5571/50000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (1820960143048723767/1821250000000000000 : ℝ)+2*(87845513563/109275000000000 : ℝ)*(5571/50000 : ℝ)=(1250024983724157/1250000000000000 : ℝ) by norm_num, show 1+2*(4552859947594703/100000000000000000000 : ℝ)=(50004552859947594703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10281391826989581/50000000000000000000 : ℝ)+(4552859947594703/100000000000000000000 : ℝ) ≤ ((1820960143048723767/1821250000000000000 : ℝ)+(87845513563/109275000000000 : ℝ)*((15513/100000 : ℝ)+(5571/50000 : ℝ)))^(4665/1024 : ℝ) := by
    rw [show (1820960143048723767/1821250000000000000 : ℝ)+(87845513563/109275000000000 : ℝ)*((15513/100000 : ℝ)+(5571/50000 : ℝ))=(2500137812961877/2500000000000000 : ℝ) by norm_num, show 1+(10281391826989581/50000000000000000000 : ℝ)+(4552859947594703/100000000000000000000 : ℝ)=(20005023128720314773/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10281391826989581/50000000000000000000 : ℝ) ≤ ((1820960143048723767/1821250000000000000 : ℝ)+2*(87845513563/109275000000000 : ℝ)*(15513/100000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (1820960143048723767/1821250000000000000 : ℝ)+2*(87845513563/109275000000000 : ℝ)*(15513/100000 : ℝ)=(31252820730943/31250000000000 : ℝ) by norm_num, show 1+2*(10281391826989581/50000000000000000000 : ℝ)=(25010281391826989581/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1820960143048723767/1821250000000000000 : ℝ)*(X 1 0+X 2 0)+(87845513563/109275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (5571/50000 : ℝ)) (hi := (15513/100000 : ℝ)) (c := (1820960143048723767/1821250000000000000 : ℝ)) (alpha := (87845513563/109275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1820960143048723767/1821250000000000000 : ℝ)*(X 0 1+X 2 1)+(87845513563/109275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (5571/50000 : ℝ)) (hi := (15513/100000 : ℝ)) (c := (1820960143048723767/1821250000000000000 : ℝ)) (alpha := (87845513563/109275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1820960143048723767/1821250000000000000 : ℝ)*(X 0 2+X 1 2)+(87845513563/109275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (5571/50000 : ℝ)) (hi := (15513/100000 : ℝ)) (c := (1820960143048723767/1821250000000000000 : ℝ)) (alpha := (87845513563/109275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-882652293/5000000000 : ℝ)*X 0 0+(5424023239/10000000000 : ℝ)*X 0 1+(5220426683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673647201/5000000000 : ℝ)*X 1 0+(-116839793/625000000 : ℝ)*X 1 1+(5220426823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347294631/10000000000 : ℝ)*X 2 0+(2610213293/5000000000 : ℝ)*X 2 1+(-1869436697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1059233791/2500000000 : ℝ)*X 0 0+(999935591/2500000000 : ℝ)*X 0 1+(560657319/1250000000 : ℝ)*X 0 2+(1059233791/2500000000 : ℝ)*X 1 0+(999935591/2500000000 : ℝ)*X 1 1+(560657319/1250000000 : ℝ)*X 1 2+(1059233791/2500000000 : ℝ)*X 2 0+(999935591/2500000000 : ℝ)*X 2 1+(560657319/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-441332757/2500000000 : ℝ)*X 0 0+(5221491743/10000000000 : ℝ)*X 0 1+(338934389/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293336419/10000000000 : ℝ)*X 1 0+(-833456423/5000000000 : ℝ)*X 1 1+(5422949919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293335829/10000000000 : ℝ)*X 2 0+(5422950287/10000000000 : ℝ)*X 2 1+(-1666913149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4236997773/10000000000 : ℝ)*X 0 0+(179308763/400000000 : ℝ)*X 0 1+(4002300881/10000000000 : ℝ)*X 0 2+(4236997773/10000000000 : ℝ)*X 1 0+(179308763/400000000 : ℝ)*X 1 1+(4002300881/10000000000 : ℝ)*X 1 2+(4236997773/10000000000 : ℝ)*X 2 0+(179308763/400000000 : ℝ)*X 2 1+(4002300881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78960170869451923145573/7285000000000000000000000000 : ℝ) := by norm_num
    linear_combination (217483333/12500000000000 : ℝ)*(base19) + (1906302589/100000000000000 : ℝ)*(base23) + (23480469/100000000000000 : ℝ)*(lower2) + (283028553/100000000000000 : ℝ)*(upper3) + (137046727/50000000000000 : ℝ)*(upper5) + (3485709215599801/100000000000000 : ℝ)*(major0) + (3485709215599801/100000000000000 : ℝ)*(major1) + (3485709215599801/100000000000000 : ℝ)*(major2) + (4911703228791701/100000000000000 : ℝ)*(sp0) + (306983248137957/6250000000000 : ℝ)*(sp1) + (4911731803771387/100000000000000 : ℝ)*(sp2) + (64364797998609/3125000000000 : ℝ)*(sp3) + (1219251291/4000000000000 : ℝ)*(sp4) + (2705969757/25000000000000 : ℝ)*(sp7) + (514921089958629/25000000000000 : ℝ)*(f.failure) + (613966713759247/12500000000000 : ℝ)*(f.sum) + (22344323286799/10927500000000000000000000000 : ℝ)*base66 + (2543327703691161101/546375000000000000000000000000000 : ℝ)*base67 + (2011788516403536101/546375000000000000000000000000000 : ℝ)*base69 + (893646694681838899/546375000000000000000000000000000 : ℝ)*base72 + (13930775974109/2731875000000000000000000000 : ℝ)*base73 + (2177646914821838899/546375000000000000000000000000000 : ℝ)*base76 + (2543401842654713899/546375000000000000000000000000000 : ℝ)*base78 + (3263559273493911101/546375000000000000000000000000000 : ℝ)*base79 + (47466171098077/21855000000000000000000000000 : ℝ)*base81 + (2746009/625000000000000000000 : ℝ)*base90 + (2746009/625000000000000000000 : ℝ)*base92 + (2746009/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (250701290530336085454443671/45531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (856442529/50000000000000 : ℝ)*(base19) + (317966203/25000000000000 : ℝ)*(base23) + (20283619/20000000000000 : ℝ)*(upper2) + (68000887/50000000000000 : ℝ)*(upper3) + (202827171/100000000000000 : ℝ)*(upper5) + (1761328909630457/50000000000000 : ℝ)*(major0) + (1761328909630457/50000000000000 : ℝ)*(major1) + (1761328909630457/50000000000000 : ℝ)*(major2) + (306507291/1250000000000 : ℝ)*(sp1) + (16736324747/100000000000000 : ℝ)*(sp2) + (2481899195066307/50000000000000 : ℝ)*(sp4) + (1240943039166069/25000000000000 : ℝ)*(sp5) + (992756076388611/20000000000000 : ℝ)*(sp6) + (2081517064851313/100000000000000 : ℝ)*(sp7) + (2081517064851313/100000000000000 : ℝ)*(f.failure) + (2481899195066307/50000000000000 : ℝ)*(f.sum) + (101978155627907/21855000000000000000000000000 : ℝ)*base66 + (2970078877891972943/273187500000000000000000000000000 : ℝ)*base68 + (1752321176957722943/273187500000000000000000000000000 : ℝ)*base70 + (4517082451054222943/273187500000000000000000000000000 : ℝ)*base72 + (15368975902483/21855000000000000000000000000 : ℝ)*base73 + (2539294470226972943/273187500000000000000000000000000 : ℝ)*base76 + (3792830903148472943/273187500000000000000000000000000 : ℝ)*base78 + (1391717423177910443/273187500000000000000000000000000 : ℝ)*base80 + (133142448966317/21855000000000000000000000000 : ℝ)*base82 + (19576827/2500000000000000000000 : ℝ)*base89 + (19576827/2500000000000000000000 : ℝ)*base91 + (19576827/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1585_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15513/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1585_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1585_s5_0 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1765324121/10000000000 : ℝ)*x 0 + (271195011/500000000 : ℝ)*x 1 + (1305134157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1765324121/10000000000 : ℝ)^4667 ≤ (1355272424333/12500000000000 : ℝ)^3643 := by
    have hnat : (1765324121 : ℕ)^4667*12500000000000^3643 ≤ 1355272424333^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765324121 10000000000 1355272424333 12500000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271195011/500000000 : ℝ)^4667 ≤ (22834955097877/50000000000000 : ℝ)^3643 := by
    have hnat : (271195011 : ℕ)^4667*50000000000000^3643 ≤ 22834955097877^3643*500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271195011 500000000 22834955097877 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305134157/2500000000 : ℝ)^4667 ≤ (108719775981/250000000000 : ℝ)^3643 := by
    have hnat : (1305134157 : ℕ)^4667*250000000000^3643 ≤ 108719775981^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305134157 2500000000 108719775981 250000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1765324121/10000000000 : ℝ), (271195011/500000000 : ℝ), (1305134157/2500000000 : ℝ)] ![(1355272424333/12500000000000 : ℝ), (22834955097877/50000000000000 : ℝ), (108719775981/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1765324121/10000000000 : ℝ)|^4667 ≤ (1355272424333/12500000000000 : ℝ)^3643
        have hw : |(-1765324121/10000000000 : ℝ)|=(1765324121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271195011/500000000 : ℝ)|^4667 ≤ (22834955097877/50000000000000 : ℝ)^3643
        have hw : |(271195011/500000000 : ℝ)|=(271195011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305134157/2500000000 : ℝ)|^4667 ≤ (108719775981/250000000000 : ℝ)^3643
        have hw : |(1305134157/2500000000 : ℝ)|=(1305134157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s5_1 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069452277/2000000000 : ℝ)*x 0 + (-1869334477/10000000000 : ℝ)*x 1 + (2610268323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069452277/2000000000 : ℝ)^4667 ≤ (44844861196527/100000000000000 : ℝ)^3643 := by
    have hnat : (1069452277 : ℕ)^4667*100000000000000^3643 ≤ 44844861196527^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069452277 2000000000 44844861196527 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1869334477/10000000000 : ℝ)^4667 ≤ (5833614100747/50000000000000 : ℝ)^3643 := by
    have hnat : (1869334477 : ℕ)^4667*50000000000000^3643 ≤ 5833614100747^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869334477 10000000000 5833614100747 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610268323/5000000000 : ℝ)^4667 ≤ (43487910584489/100000000000000 : ℝ)^3643 := by
    have hnat : (2610268323 : ℕ)^4667*100000000000000^3643 ≤ 43487910584489^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610268323 5000000000 43487910584489 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069452277/2000000000 : ℝ), (-1869334477/10000000000 : ℝ), (2610268323/5000000000 : ℝ)] ![(44844861196527/100000000000000 : ℝ), (5833614100747/50000000000000 : ℝ), (43487910584489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069452277/2000000000 : ℝ)|^4667 ≤ (44844861196527/100000000000000 : ℝ)^3643
        have hw : |(1069452277/2000000000 : ℝ)|=(1069452277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1869334477/10000000000 : ℝ)|^4667 ≤ (5833614100747/50000000000000 : ℝ)^3643
        have hw : |(-1869334477/10000000000 : ℝ)|=(1869334477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610268323/5000000000 : ℝ)|^4667 ≤ (43487910584489/100000000000000 : ℝ)^3643
        have hw : |(2610268323/5000000000 : ℝ)|=(2610268323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s5_2 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347261401/10000000000 : ℝ)*x 0 + (2610268341/5000000000 : ℝ)*x 1 + (-233666801/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347261401/10000000000 : ℝ)^4667 ≤ (44844861368429/100000000000000 : ℝ)^3643 := by
    have hnat : (5347261401 : ℕ)^4667*100000000000000^3643 ≤ 44844861368429^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347261401 10000000000 44844861368429 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610268341/5000000000 : ℝ)^4667 ≤ (43487910968669/100000000000000 : ℝ)^3643 := by
    have hnat : (2610268341 : ℕ)^4667*100000000000000^3643 ≤ 43487910968669^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610268341 5000000000 43487910968669 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233666801/1250000000 : ℝ)^4667 ≤ (11667227649787/100000000000000 : ℝ)^3643 := by
    have hnat : (233666801 : ℕ)^4667*100000000000000^3643 ≤ 11667227649787^3643*1250000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233666801 1250000000 11667227649787 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347261401/10000000000 : ℝ), (2610268341/5000000000 : ℝ), (-233666801/1250000000 : ℝ)] ![(44844861368429/100000000000000 : ℝ), (43487910968669/100000000000000 : ℝ), (11667227649787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347261401/10000000000 : ℝ)|^4667 ≤ (44844861368429/100000000000000 : ℝ)^3643
        have hw : |(5347261401/10000000000 : ℝ)|=(5347261401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610268341/5000000000 : ℝ)|^4667 ≤ (43487910968669/100000000000000 : ℝ)^3643
        have hw : |(2610268341/5000000000 : ℝ)|=(2610268341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-233666801/1250000000 : ℝ)|^4667 ≤ (11667227649787/100000000000000 : ℝ)^3643
        have hw : |(-233666801/1250000000 : ℝ)|=(233666801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s5_3 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4236946563/10000000000 : ℝ)*x 0 + (4000018559/10000000000 : ℝ)*x 1 + (2242489943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4236946563/10000000000 : ℝ)^4667 ≤ (16641498408667/50000000000000 : ℝ)^3643 := by
    have hnat : (4236946563 : ℕ)^4667*50000000000000^3643 ≤ 16641498408667^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236946563 10000000000 16641498408667 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4000018559/10000000000 : ℝ)^4667 ≤ (15458836624887/50000000000000 : ℝ)^3643 := by
    have hnat : (4000018559 : ℕ)^4667*50000000000000^3643 ≤ 15458836624887^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4000018559 10000000000 15458836624887 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242489943/5000000000 : ℝ)^4667 ≤ (35799329909993/100000000000000 : ℝ)^3643 := by
    have hnat : (2242489943 : ℕ)^4667*100000000000000^3643 ≤ 35799329909993^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242489943 5000000000 35799329909993 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4236946563/10000000000 : ℝ), (4000018559/10000000000 : ℝ), (2242489943/5000000000 : ℝ)] ![(16641498408667/50000000000000 : ℝ), (15458836624887/50000000000000 : ℝ), (35799329909993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4236946563/10000000000 : ℝ)|^4667 ≤ (16641498408667/50000000000000 : ℝ)^3643
        have hw : |(4236946563/10000000000 : ℝ)|=(4236946563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4000018559/10000000000 : ℝ)|^4667 ≤ (15458836624887/50000000000000 : ℝ)^3643
        have hw : |(4000018559/10000000000 : ℝ)|=(4000018559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242489943/5000000000 : ℝ)|^4667 ≤ (35799329909993/100000000000000 : ℝ)^3643
        have hw : |(2242489943/5000000000 : ℝ)|=(2242489943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s5_4 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1765350339/10000000000 : ℝ)*x 0 + (5221599339/10000000000 : ℝ)*x 1 + (67785371/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1765350339/10000000000 : ℝ)^4667 ≤ (2710596420341/25000000000000 : ℝ)^3643 := by
    have hnat : (1765350339 : ℕ)^4667*25000000000000^3643 ≤ 2710596420341^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765350339 10000000000 2710596420341 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221599339/10000000000 : ℝ)^4667 ≤ (21749625804211/50000000000000 : ℝ)^3643 := by
    have hnat : (5221599339 : ℕ)^4667*50000000000000^3643 ≤ 21749625804211^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221599339 10000000000 21749625804211 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67785371/125000000 : ℝ)^4667 ≤ (45658362696393/100000000000000 : ℝ)^3643 := by
    have hnat : (67785371 : ℕ)^4667*100000000000000^3643 ≤ 45658362696393^3643*125000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67785371 125000000 45658362696393 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1765350339/10000000000 : ℝ), (5221599339/10000000000 : ℝ), (67785371/125000000 : ℝ)] ![(2710596420341/25000000000000 : ℝ), (21749625804211/50000000000000 : ℝ), (45658362696393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1765350339/10000000000 : ℝ)|^4667 ≤ (2710596420341/25000000000000 : ℝ)^3643
        have hw : |(-1765350339/10000000000 : ℝ)|=(1765350339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221599339/10000000000 : ℝ)|^4667 ≤ (21749625804211/50000000000000 : ℝ)^3643
        have hw : |(5221599339/10000000000 : ℝ)|=(5221599339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67785371/125000000 : ℝ)|^4667 ≤ (45658362696393/100000000000000 : ℝ)^3643
        have hw : |(67785371/125000000 : ℝ)|=(67785371/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s5_5 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293364601/10000000000 : ℝ)*x 0 + (-1667041359/10000000000 : ℝ)*x 1 + (5422829681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293364601/10000000000 : ℝ)^4667 ≤ (22133312278777/50000000000000 : ℝ)^3643 := by
    have hnat : (5293364601 : ℕ)^4667*50000000000000^3643 ≤ 22133312278777^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293364601 10000000000 22133312278777 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1667041359/10000000000 : ℝ)^4667 ≤ (5037506355831/50000000000000 : ℝ)^3643 := by
    have hnat : (1667041359 : ℕ)^4667*50000000000000^3643 ≤ 5037506355831^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667041359 10000000000 5037506355831 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422829681/10000000000 : ℝ)^4667 ≤ (45658362707179/100000000000000 : ℝ)^3643 := by
    have hnat : (5422829681 : ℕ)^4667*100000000000000^3643 ≤ 45658362707179^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422829681 10000000000 45658362707179 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293364601/10000000000 : ℝ), (-1667041359/10000000000 : ℝ), (5422829681/10000000000 : ℝ)] ![(22133312278777/50000000000000 : ℝ), (5037506355831/50000000000000 : ℝ), (45658362707179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293364601/10000000000 : ℝ)|^4667 ≤ (22133312278777/50000000000000 : ℝ)^3643
        have hw : |(5293364601/10000000000 : ℝ)|=(5293364601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1667041359/10000000000 : ℝ)|^4667 ≤ (5037506355831/50000000000000 : ℝ)^3643
        have hw : |(-1667041359/10000000000 : ℝ)|=(1667041359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422829681/10000000000 : ℝ)|^4667 ≤ (45658362707179/100000000000000 : ℝ)^3643
        have hw : |(5422829681/10000000000 : ℝ)|=(5422829681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s5_6 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293364599/10000000000 : ℝ)*x 0 + (1355707421/2500000000 : ℝ)*x 1 + (-1667041359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293364599/10000000000 : ℝ)^4667 ≤ (44266624536127/100000000000000 : ℝ)^3643 := by
    have hnat : (5293364599 : ℕ)^4667*100000000000000^3643 ≤ 44266624536127^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293364599 10000000000 44266624536127 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355707421/2500000000 : ℝ)^4667 ≤ (22829181369769/50000000000000 : ℝ)^3643 := by
    have hnat : (1355707421 : ℕ)^4667*50000000000000^3643 ≤ 22829181369769^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355707421 2500000000 22829181369769 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1667041359/10000000000 : ℝ)^4667 ≤ (5037506355831/50000000000000 : ℝ)^3643 := by
    have hnat : (1667041359 : ℕ)^4667*50000000000000^3643 ≤ 5037506355831^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667041359 10000000000 5037506355831 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293364599/10000000000 : ℝ), (1355707421/2500000000 : ℝ), (-1667041359/10000000000 : ℝ)] ![(44266624536127/100000000000000 : ℝ), (22829181369769/50000000000000 : ℝ), (5037506355831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293364599/10000000000 : ℝ)|^4667 ≤ (44266624536127/100000000000000 : ℝ)^3643
        have hw : |(5293364599/10000000000 : ℝ)|=(5293364599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355707421/2500000000 : ℝ)|^4667 ≤ (22829181369769/50000000000000 : ℝ)^3643
        have hw : |(1355707421/2500000000 : ℝ)|=(1355707421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1667041359/10000000000 : ℝ)|^4667 ≤ (5037506355831/50000000000000 : ℝ)^3643
        have hw : |(-1667041359/10000000000 : ℝ)|=(1667041359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s5_7 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4237009079/10000000000 : ℝ)*x 0 + (448244589/1000000000 : ℝ)*x 1 + (2001285709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237009079/10000000000 : ℝ)^4667 ≤ (16641812973489/50000000000000 : ℝ)^3643 := by
    have hnat : (4237009079 : ℕ)^4667*50000000000000^3643 ≤ 16641812973489^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237009079 10000000000 16641812973489 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448244589/1000000000 : ℝ)^4667 ≤ (286187360689/800000000000 : ℝ)^3643 := by
    have hnat : (448244589 : ℕ)^4667*800000000000^3643 ≤ 286187360689^3643*1000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448244589 1000000000 286187360689 800000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2001285709/5000000000 : ℝ)^4667 ≤ (30942953955991/100000000000000 : ℝ)^3643 := by
    have hnat : (2001285709 : ℕ)^4667*100000000000000^3643 ≤ 30942953955991^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001285709 5000000000 30942953955991 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237009079/10000000000 : ℝ), (448244589/1000000000 : ℝ), (2001285709/5000000000 : ℝ)] ![(16641812973489/50000000000000 : ℝ), (286187360689/800000000000 : ℝ), (30942953955991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237009079/10000000000 : ℝ)|^4667 ≤ (16641812973489/50000000000000 : ℝ)^3643
        have hw : |(4237009079/10000000000 : ℝ)|=(4237009079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448244589/1000000000 : ℝ)|^4667 ≤ (286187360689/800000000000 : ℝ)^3643
        have hw : |(448244589/1000000000 : ℝ)|=(448244589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2001285709/5000000000 : ℝ)|^4667 ≤ (30942953955991/100000000000000 : ℝ)^3643
        have hw : |(2001285709/5000000000 : ℝ)|=(2001285709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1585_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11169/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5583/50000 : ℝ) ^ (4665/1024 : ℝ) ≤ (183908334319927/4000000000000000000 : ℝ) := by
    have hpowers : (5583/50000 : ℝ)^4665 ≤ (183908334319927/4000000000000000000 : ℝ)^1024 := by
      have hnat : (5583 : ℕ)^4665*4000000000000000000^1024 ≤ 183908334319927^1024*50000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5583 50000 183908334319927 4000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5583/50000 : ℝ)) (X := (183908334319927/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7743/50000 : ℝ) ^ (4665/1024 : ℝ) ≤ (816009785053367/4000000000000000000 : ℝ) := by
    have hpowers : (7743/50000 : ℝ)^4665 ≤ (816009785053367/4000000000000000000 : ℝ)^1024 := by
      have hnat : (7743 : ℕ)^4665*4000000000000000000^1024 ≤ 816009785053367^1024*50000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7743 50000 816009785053367 4000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7743/50000 : ℝ)) (X := (816009785053367/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000183908334319927/2000000000000000000 : ℝ) ≤ (2500050459640089/2500000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (2000183908334319927/2000000000000000000 : ℝ)^1024 ≤ (2500050459640089/2500000000000000 : ℝ)^4665 := by
      have hnat : (2000183908334319927 : ℕ)^1024*2500000000000000^4665 ≤ 2500050459640089^4665*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000183908334319927 2000000000000000000 2500050459640089 2500000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500050459640089/2500000000000000 : ℝ)) (X := (2000183908334319927/2000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000499959059686647/2000000000000000000 : ℝ) ≤ (500027433448079/500000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (2000499959059686647/2000000000000000000 : ℝ)^1024 ≤ (500027433448079/500000000000000 : ℝ)^4665 := by
      have hnat : (2000499959059686647 : ℕ)^1024*500000000000000^4665 ≤ 500027433448079^4665*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000499959059686647 2000000000000000000 500027433448079 500000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500027433448079/500000000000000 : ℝ)) (X := (2000499959059686647/2000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000816009785053367/2000000000000000000 : ℝ) ≤ (2500223874840701/2500000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (2000816009785053367/2000000000000000000 : ℝ)^1024 ≤ (2500223874840701/2500000000000000 : ℝ)^4665 := by
      have hnat : (2000816009785053367 : ℕ)^1024*2500000000000000^4665 ≤ 2500223874840701^4665*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000816009785053367 2000000000000000000 2500223874840701 2500000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500223874840701/2500000000000000 : ℝ)) (X := (2000816009785053367/2000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(183908334319927/4000000000000000000 : ℝ) ≤ ((449928401313131287/450000000000000000 : ℝ)+2*(43353800153/54000000000000 : ℝ)*(5583/50000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (449928401313131287/450000000000000000 : ℝ)+2*(43353800153/54000000000000 : ℝ)*(5583/50000 : ℝ)=(2500050459640089/2500000000000000 : ℝ) by norm_num, show 1+2*(183908334319927/4000000000000000000 : ℝ)=(2000183908334319927/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(816009785053367/4000000000000000000 : ℝ)+(183908334319927/4000000000000000000 : ℝ) ≤ ((449928401313131287/450000000000000000 : ℝ)+(43353800153/54000000000000 : ℝ)*((7743/50000 : ℝ)+(5583/50000 : ℝ)))^(4665/1024 : ℝ) := by
    rw [show (449928401313131287/450000000000000000 : ℝ)+(43353800153/54000000000000 : ℝ)*((7743/50000 : ℝ)+(5583/50000 : ℝ))=(500027433448079/500000000000000 : ℝ) by norm_num, show 1+(816009785053367/4000000000000000000 : ℝ)+(183908334319927/4000000000000000000 : ℝ)=(2000499959059686647/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(816009785053367/4000000000000000000 : ℝ) ≤ ((449928401313131287/450000000000000000 : ℝ)+2*(43353800153/54000000000000 : ℝ)*(7743/50000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (449928401313131287/450000000000000000 : ℝ)+2*(43353800153/54000000000000 : ℝ)*(7743/50000 : ℝ)=(2500223874840701/2500000000000000 : ℝ) by norm_num, show 1+2*(816009785053367/4000000000000000000 : ℝ)=(2000816009785053367/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (449928401313131287/450000000000000000 : ℝ)*(X 1 0+X 2 0)+(43353800153/54000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (449928401313131287/450000000000000000 : ℝ)) (alpha := (43353800153/54000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (449928401313131287/450000000000000000 : ℝ)*(X 0 1+X 2 1)+(43353800153/54000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (449928401313131287/450000000000000000 : ℝ)) (alpha := (43353800153/54000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (449928401313131287/450000000000000000 : ℝ)*(X 0 2+X 1 2)+(43353800153/54000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (449928401313131287/450000000000000000 : ℝ)) (alpha := (43353800153/54000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1765324121/10000000000 : ℝ)*X 0 0+(271195011/500000000 : ℝ)*X 0 1+(1305134157/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069452277/2000000000 : ℝ)*X 1 0+(-1869334477/10000000000 : ℝ)*X 1 1+(2610268323/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347261401/10000000000 : ℝ)*X 2 0+(2610268341/5000000000 : ℝ)*X 2 1+(-233666801/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4236946563/10000000000 : ℝ)*X 0 0+(4000018559/10000000000 : ℝ)*X 0 1+(2242489943/5000000000 : ℝ)*X 0 2+(4236946563/10000000000 : ℝ)*X 1 0+(4000018559/10000000000 : ℝ)*X 1 1+(2242489943/5000000000 : ℝ)*X 1 2+(4236946563/10000000000 : ℝ)*X 2 0+(4000018559/10000000000 : ℝ)*X 2 1+(2242489943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1765350339/10000000000 : ℝ)*X 0 0+(5221599339/10000000000 : ℝ)*X 0 1+(67785371/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293364601/10000000000 : ℝ)*X 1 0+(-1667041359/10000000000 : ℝ)*X 1 1+(5422829681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293364599/10000000000 : ℝ)*X 2 0+(1355707421/2500000000 : ℝ)*X 2 1+(-1667041359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4237009079/10000000000 : ℝ)*X 0 0+(448244589/1000000000 : ℝ)*X 0 1+(2001285709/5000000000 : ℝ)*X 0 2+(4237009079/10000000000 : ℝ)*X 1 0+(448244589/1000000000 : ℝ)*X 1 1+(2001285709/5000000000 : ℝ)*X 1 2+(4237009079/10000000000 : ℝ)*X 2 0+(448244589/1000000000 : ℝ)*X 2 1+(2001285709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47473759622834989506744353/11250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (341043569/50000000000000 : ℝ)*(base19) + (644164011/100000000000000 : ℝ)*(base23) + (7036551/25000000000000 : ℝ)*(lower2) + (92385949/100000000000000 : ℝ)*(upper3) + (3184071/2500000000000 : ℝ)*(upper5) + (1744837851892573/50000000000000 : ℝ)*(major0) + (1744837851892573/50000000000000 : ℝ)*(major1) + (1744837851892573/50000000000000 : ℝ)*(major2) + (4917311147453331/100000000000000 : ℝ)*(sp0) + (2458661225629413/50000000000000 : ℝ)*(sp1) + (4917322489181953/100000000000000 : ℝ)*(sp2) + (1031012087895463/50000000000000 : ℝ)*(sp3) + (11985892633/100000000000000 : ℝ)*(sp4) + (4947213/125000000000 : ℝ)*(sp7) + (1031014066780663/50000000000000 : ℝ)*(f.failure) + (1229330783336491/25000000000000 : ℝ)*(f.sum) + (6468342908669/1350000000000000000000000000 : ℝ)*base65 + (320214655631919353/67500000000000000000000000000000 : ℝ)*base67 + (74194509679419353/67500000000000000000000000000000 : ℝ)*base69 + (588951545590580647/67500000000000000000000000000000 : ℝ)*base72 + (10848271660469/1350000000000000000000000000 : ℝ)*base73 + (265471044760580647/67500000000000000000000000000000 : ℝ)*base76 + (78142740243080647/67500000000000000000000000000000 : ℝ)*base78 + (1000118928250580647/67500000000000000000000000000000 : ℝ)*base80 + (9866693167469/1350000000000000000000000000 : ℝ)*base81 + (12659523/1250000000000000000000 : ℝ)*base90 + (12659523/1250000000000000000000 : ℝ)*base92 + (12659523/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48770549531858689079988539/3750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (201569967/10000000000000 : ℝ)*(base19) + (2187980019/100000000000000 : ℝ)*(base23) + (327379401/50000000000000 : ℝ)*(lower1) + (268358209/100000000000000 : ℝ)*(upper3) + (78610787/100000000000000 : ℝ)*(lower4) + (66606701/25000000000000 : ℝ)*(upper5) + (1763315027391601/50000000000000 : ℝ)*(major0) + (1763315027391601/50000000000000 : ℝ)*(major1) + (1763315027391601/50000000000000 : ℝ)*(major2) + (503828249/20000000000000 : ℝ)*(sp2) + (99387908828117/2000000000000 : ℝ)*(sp4) + (248469671285309/5000000000000 : ℝ)*(sp5) + (2484695367142293/50000000000000 : ℝ)*(sp6) + (2083864234644541/100000000000000 : ℝ)*(sp7) + (2083864234644541/100000000000000 : ℝ)*(f.failure) + (99387908828117/2000000000000 : ℝ)*(f.sum) + (4952673519803/1350000000000000000000000000 : ℝ)*base65 + (2808180261996186461/67500000000000000000000000000000 : ℝ)*base67 + (105342730881186461/67500000000000000000000000000000 : ℝ)*base69 + (3081069108163686461/67500000000000000000000000000000 : ℝ)*base71 + (7715066090453/1350000000000000000000000000 : ℝ)*base73 + (983956441731186461/67500000000000000000000000000000 : ℝ)*base75 + (412090685331186461/67500000000000000000000000000000 : ℝ)*base77 + (342043005426186461/67500000000000000000000000000000 : ℝ)*base79 + (6914258329553/1350000000000000000000000000 : ℝ)*base81 + (21274561/2500000000000000000000 : ℝ)*base90 + (21274561/2500000000000000000000 : ℝ)*base92 + (21274561/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1585_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1585_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1585_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7887/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1585_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1585_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1585_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7887/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1585_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
