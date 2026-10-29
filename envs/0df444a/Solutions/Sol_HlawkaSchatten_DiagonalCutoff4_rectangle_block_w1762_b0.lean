-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1762_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:29:10.506142+00:00
-- url     : https://prove2.me/submissions/542c5993-ab47-40c4-8091-e4e2fb545c80

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
theorem support_rectangle_w1762_s0_0 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-280485363/2500000000 : ℝ)*x 0 + (44762239/80000000 : ℝ)*x 1 + (624349593/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280485363/2500000000 : ℝ)^5967 ≤ (7131164566481/100000000000000 : ℝ)^4943 := by
    have hnat : (280485363 : ℕ)^5967*100000000000000^4943 ≤ 7131164566481^4943*2500000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280485363 2500000000 7131164566481 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44762239/80000000 : ℝ)^5967 ≤ (1550351555423/3125000000000 : ℝ)^4943 := by
    have hnat : (44762239 : ℕ)^5967*3125000000000^4943 ≤ 1550351555423^4943*80000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44762239 80000000 1550351555423 3125000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624349593/1250000000 : ℝ)^5967 ≤ (4325758564069/10000000000000 : ℝ)^4943 := by
    have hnat : (624349593 : ℕ)^5967*10000000000000^4943 ≤ 4325758564069^4943*1250000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624349593 1250000000 4325758564069 10000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-280485363/2500000000 : ℝ), (44762239/80000000 : ℝ), (624349593/1250000000 : ℝ)] ![(7131164566481/100000000000000 : ℝ), (1550351555423/3125000000000 : ℝ), (4325758564069/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-280485363/2500000000 : ℝ)|^5967 ≤ (7131164566481/100000000000000 : ℝ)^4943
        have hw : |(-280485363/2500000000 : ℝ)|=(280485363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44762239/80000000 : ℝ)|^5967 ≤ (1550351555423/3125000000000 : ℝ)^4943
        have hw : |(44762239/80000000 : ℝ)|=(44762239/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(624349593/1250000000 : ℝ)|^5967 ≤ (4325758564069/10000000000000 : ℝ)^4943
        have hw : |(624349593/1250000000 : ℝ)|=(624349593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s0_1 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358233283/10000000000 : ℝ)*x 0 + (-721153977/5000000000 : ℝ)*x 1 + (2497398957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358233283/10000000000 : ℝ)^5967 ≤ (2942830904653/6250000000000 : ℝ)^4943 := by
    have hnat : (5358233283 : ℕ)^5967*6250000000000^4943 ≤ 2942830904653^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358233283 10000000000 2942830904653 6250000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721153977/5000000000 : ℝ)^5967 ≤ (193142152771/2000000000000 : ℝ)^4943 := by
    have hnat : (721153977 : ℕ)^5967*2000000000000^4943 ≤ 193142152771^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721153977 5000000000 193142152771 2000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2497398957/5000000000 : ℝ)^5967 ≤ (21628798936321/50000000000000 : ℝ)^4943 := by
    have hnat : (2497398957 : ℕ)^5967*50000000000000^4943 ≤ 21628798936321^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497398957 5000000000 21628798936321 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358233283/10000000000 : ℝ), (-721153977/5000000000 : ℝ), (2497398957/5000000000 : ℝ)] ![(2942830904653/6250000000000 : ℝ), (193142152771/2000000000000 : ℝ), (21628798936321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358233283/10000000000 : ℝ)|^5967 ≤ (2942830904653/6250000000000 : ℝ)^4943
        have hw : |(5358233283/10000000000 : ℝ)|=(5358233283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-721153977/5000000000 : ℝ)|^5967 ≤ (193142152771/2000000000000 : ℝ)^4943
        have hw : |(-721153977/5000000000 : ℝ)|=(721153977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2497398957/5000000000 : ℝ)|^5967 ≤ (21628798936321/50000000000000 : ℝ)^4943
        have hw : |(2497398957/5000000000 : ℝ)|=(2497398957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s0_2 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358237069/10000000000 : ℝ)*x 0 + (49947953/100000000 : ℝ)*x 1 + (-1442306367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358237069/10000000000 : ℝ)^5967 ≤ (47085334635931/100000000000000 : ℝ)^4943 := by
    have hnat : (5358237069 : ℕ)^5967*100000000000000^4943 ≤ 47085334635931^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358237069 10000000000 47085334635931 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49947953/100000000 : ℝ)^5967 ≤ (43257570544163/100000000000000 : ℝ)^4943 := by
    have hnat : (49947953 : ℕ)^5967*100000000000000^4943 ≤ 43257570544163^4943*100000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49947953 100000000 43257570544163 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1442306367/10000000000 : ℝ)^5967 ≤ (1931418962273/20000000000000 : ℝ)^4943 := by
    have hnat : (1442306367 : ℕ)^5967*20000000000000^4943 ≤ 1931418962273^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1442306367 10000000000 1931418962273 20000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358237069/10000000000 : ℝ), (49947953/100000000 : ℝ), (-1442306367/10000000000 : ℝ)] ![(47085334635931/100000000000000 : ℝ), (43257570544163/100000000000000 : ℝ), (1931418962273/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358237069/10000000000 : ℝ)|^5967 ≤ (47085334635931/100000000000000 : ℝ)^4943
        have hw : |(5358237069/10000000000 : ℝ)|=(5358237069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(49947953/100000000 : ℝ)|^5967 ≤ (43257570544163/100000000000000 : ℝ)^4943
        have hw : |(49947953/100000000 : ℝ)|=(49947953/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1442306367/10000000000 : ℝ)|^5967 ≤ (1931418962273/20000000000000 : ℝ)^4943
        have hw : |(-1442306367/10000000000 : ℝ)|=(1442306367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s0_3 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3960135617/10000000000 : ℝ)*x 0 + (1497302929/5000000000 : ℝ)*x 1 + (1012881483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3960135617/10000000000 : ℝ)^5967 ≤ (32686695234987/100000000000000 : ℝ)^4943 := by
    have hnat : (3960135617 : ℕ)^5967*100000000000000^4943 ≤ 32686695234987^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3960135617 10000000000 32686695234987 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1497302929/5000000000 : ℝ)^5967 ≤ (23326916542599/100000000000000 : ℝ)^4943 := by
    have hnat : (1497302929 : ℕ)^5967*100000000000000^4943 ≤ 23326916542599^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1497302929 5000000000 23326916542599 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1012881483/2000000000 : ℝ)^5967 ≤ (10996597052071/25000000000000 : ℝ)^4943 := by
    have hnat : (1012881483 : ℕ)^5967*25000000000000^4943 ≤ 10996597052071^4943*2000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012881483 2000000000 10996597052071 25000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3960135617/10000000000 : ℝ), (1497302929/5000000000 : ℝ), (1012881483/2000000000 : ℝ)] ![(32686695234987/100000000000000 : ℝ), (23326916542599/100000000000000 : ℝ), (10996597052071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3960135617/10000000000 : ℝ)|^5967 ≤ (32686695234987/100000000000000 : ℝ)^4943
        have hw : |(3960135617/10000000000 : ℝ)|=(3960135617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1497302929/5000000000 : ℝ)|^5967 ≤ (23326916542599/100000000000000 : ℝ)^4943
        have hw : |(1497302929/5000000000 : ℝ)|=(1497302929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1012881483/2000000000 : ℝ)|^5967 ≤ (10996597052071/25000000000000 : ℝ)^4943
        have hw : |(1012881483/2000000000 : ℝ)|=(1012881483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s0_4 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1123077299/10000000000 : ℝ)*x 0 + (500980729/1000000000 : ℝ)*x 1 + (1394948727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123077299/10000000000 : ℝ)^5967 ≤ (1427976128683/20000000000000 : ℝ)^4943 := by
    have hnat : (1123077299 : ℕ)^5967*20000000000000^4943 ≤ 1427976128683^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123077299 10000000000 1427976128683 20000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500980729/1000000000 : ℝ)^5967 ≤ (8682912919199/20000000000000 : ℝ)^4943 := by
    have hnat : (500980729 : ℕ)^5967*20000000000000^4943 ≤ 8682912919199^4943*1000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500980729 1000000000 8682912919199 20000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1394948727/2500000000 : ℝ)^5967 ≤ (772586792997/1562500000000 : ℝ)^4943 := by
    have hnat : (1394948727 : ℕ)^5967*1562500000000^4943 ≤ 772586792997^4943*2500000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394948727 2500000000 772586792997 1562500000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1123077299/10000000000 : ℝ), (500980729/1000000000 : ℝ), (1394948727/2500000000 : ℝ)] ![(1427976128683/20000000000000 : ℝ), (8682912919199/20000000000000 : ℝ), (772586792997/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1123077299/10000000000 : ℝ)|^5967 ≤ (1427976128683/20000000000000 : ℝ)^4943
        have hw : |(-1123077299/10000000000 : ℝ)|=(1123077299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(500980729/1000000000 : ℝ)|^5967 ≤ (8682912919199/20000000000000 : ℝ)^4943
        have hw : |(500980729/1000000000 : ℝ)|=(500980729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1394948727/2500000000 : ℝ)|^5967 ≤ (772586792997/1562500000000 : ℝ)^4943
        have hw : |(1394948727/2500000000 : ℝ)|=(1394948727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s0_5 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198931223/10000000000 : ℝ)*x 0 + (-857309373/10000000000 : ℝ)*x 1 + (1394948719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198931223/10000000000 : ℝ)^5967 ≤ (5675085091671/12500000000000 : ℝ)^4943 := by
    have hnat : (5198931223 : ℕ)^5967*12500000000000^4943 ≤ 5675085091671^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198931223 10000000000 5675085091671 12500000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (857309373/10000000000 : ℝ)^5967 ≤ (5153764844827/100000000000000 : ℝ)^4943 := by
    have hnat : (857309373 : ℕ)^5967*100000000000000^4943 ≤ 5153764844827^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857309373 10000000000 5153764844827 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1394948719/2500000000 : ℝ)^5967 ≤ (24722777204747/50000000000000 : ℝ)^4943 := by
    have hnat : (1394948719 : ℕ)^5967*50000000000000^4943 ≤ 24722777204747^4943*2500000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394948719 2500000000 24722777204747 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198931223/10000000000 : ℝ), (-857309373/10000000000 : ℝ), (1394948719/2500000000 : ℝ)] ![(5675085091671/12500000000000 : ℝ), (5153764844827/100000000000000 : ℝ), (24722777204747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198931223/10000000000 : ℝ)|^5967 ≤ (5675085091671/12500000000000 : ℝ)^4943
        have hw : |(5198931223/10000000000 : ℝ)|=(5198931223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-857309373/10000000000 : ℝ)|^5967 ≤ (5153764844827/100000000000000 : ℝ)^4943
        have hw : |(-857309373/10000000000 : ℝ)|=(857309373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1394948719/2500000000 : ℝ)|^5967 ≤ (24722777204747/50000000000000 : ℝ)^4943
        have hw : |(1394948719/2500000000 : ℝ)|=(1394948719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s0_6 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599465721/5000000000 : ℝ)*x 0 + (223191797/400000000 : ℝ)*x 1 + (-428654491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599465721/5000000000 : ℝ)^5967 ≤ (45400683042017/100000000000000 : ℝ)^4943 := by
    have hnat : (2599465721 : ℕ)^5967*100000000000000^4943 ≤ 45400683042017^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599465721 5000000000 45400683042017 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223191797/400000000 : ℝ)^5967 ≤ (24722777466831/50000000000000 : ℝ)^4943 := by
    have hnat : (223191797 : ℕ)^5967*50000000000000^4943 ≤ 24722777466831^4943*400000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223191797 400000000 24722777466831 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428654491/5000000000 : ℝ)^5967 ≤ (515376200737/10000000000000 : ℝ)^4943 := by
    have hnat : (428654491 : ℕ)^5967*10000000000000^4943 ≤ 515376200737^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428654491 5000000000 515376200737 10000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599465721/5000000000 : ℝ), (223191797/400000000 : ℝ), (-428654491/5000000000 : ℝ)] ![(45400683042017/100000000000000 : ℝ), (24722777466831/50000000000000 : ℝ), (515376200737/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599465721/5000000000 : ℝ)|^5967 ≤ (45400683042017/100000000000000 : ℝ)^4943
        have hw : |(2599465721/5000000000 : ℝ)|=(2599465721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223191797/400000000 : ℝ)|^5967 ≤ (24722777466831/50000000000000 : ℝ)^4943
        have hw : |(223191797/400000000 : ℝ)|=(223191797/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428654491/5000000000 : ℝ)|^5967 ≤ (515376200737/10000000000000 : ℝ)^4943
        have hw : |(-428654491/5000000000 : ℝ)|=(428654491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s0_7 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3964056461/10000000000 : ℝ)*x 0 + (1002533029/2000000000 : ℝ)*x 1 + (3047983833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3964056461/10000000000 : ℝ)^5967 ≤ (3272576587/10000000000 : ℝ)^4943 := by
    have hnat : (3964056461 : ℕ)^5967*10000000000^4943 ≤ 3272576587^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3964056461 10000000000 3272576587 10000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002533029/2000000000 : ℝ)^5967 ≤ (10861115710377/25000000000000 : ℝ)^4943 := by
    have hnat : (1002533029 : ℕ)^5967*25000000000000^4943 ≤ 10861115710377^4943*2000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002533029 2000000000 10861115710377 25000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3047983833/10000000000 : ℝ)^5967 ≤ (5957442819521/25000000000000 : ℝ)^4943 := by
    have hnat : (3047983833 : ℕ)^5967*25000000000000^4943 ≤ 5957442819521^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3047983833 10000000000 5957442819521 25000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3964056461/10000000000 : ℝ), (1002533029/2000000000 : ℝ), (3047983833/10000000000 : ℝ)] ![(3272576587/10000000000 : ℝ), (10861115710377/25000000000000 : ℝ), (5957442819521/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3964056461/10000000000 : ℝ)|^5967 ≤ (3272576587/10000000000 : ℝ)^4943
        have hw : |(3964056461/10000000000 : ℝ)|=(3964056461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1002533029/2000000000 : ℝ)|^5967 ≤ (10861115710377/25000000000000 : ℝ)^4943
        have hw : |(1002533029/2000000000 : ℝ)|=(1002533029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3047983833/10000000000 : ℝ)|^5967 ≤ (5957442819521/25000000000000 : ℝ)^4943
        have hw : |(3047983833/10000000000 : ℝ)|=(3047983833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1762_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (55586051/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1793/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20193/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5951/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5951 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5951*1^1024 ≤ 0^1024*1^5951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5951/1024 : ℝ) ≤ (486813163252972823/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5951 ≤ (486813163252972823/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5951*100000000000000000000^1024 ≤ 486813163252972823^1024*5^5951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 486813163252972823 100000000000000000000 5951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (486813163252972823/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5951/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5951 := by
      have hnat : (1 : ℕ)^1024*1^5951 ≤ 1^5951*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100486813163252972823/100000000000000000000 : ℝ) ≤ (2502089964134501/2500000000000000 : ℝ) ^ (5951/1024 : ℝ) := by
    have hpowers : (100486813163252972823/100000000000000000000 : ℝ)^1024 ≤ (2502089964134501/2500000000000000 : ℝ)^5951 := by
      have hnat : (100486813163252972823 : ℕ)^1024*2500000000000000^5951 ≤ 2502089964134501^5951*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100486813163252972823 100000000000000000000 2502089964134501 2500000000000000 1024 5951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502089964134501/2500000000000000 : ℝ)) (X := (100486813163252972823/100000000000000000000 : ℝ)) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50486813163252972823/50000000000000000000 : ℝ) ≤ (1252089964134501/1250000000000000 : ℝ) ^ (5951/1024 : ℝ) := by
    have hpowers : (50486813163252972823/50000000000000000000 : ℝ)^1024 ≤ (1252089964134501/1250000000000000 : ℝ)^5951 := by
      have hnat : (50486813163252972823 : ℕ)^1024*1250000000000000^5951 ≤ 1252089964134501^5951*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50486813163252972823 50000000000000000000 1252089964134501 1250000000000000 1024 5951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252089964134501/1250000000000000 : ℝ)) (X := (50486813163252972823/50000000000000000000 : ℝ)) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2089964134501/1000000000000000 : ℝ)*(0 : ℝ))^(5951/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2089964134501/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(486813163252972823/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2089964134501/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5951/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2089964134501/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2502089964134501/2500000000000000 : ℝ) by norm_num, show 1+(486813163252972823/100000000000000000000 : ℝ)+(0 : ℝ)=(100486813163252972823/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(486813163252972823/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2089964134501/1000000000000000 : ℝ)*(2/5 : ℝ))^(5951/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2089964134501/1000000000000000 : ℝ)*(2/5 : ℝ)=(1252089964134501/1250000000000000 : ℝ) by norm_num, show 1+2*(486813163252972823/100000000000000000000 : ℝ)=(50486813163252972823/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2089964134501/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5951/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2089964134501/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2089964134501/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5951/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2089964134501/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2089964134501/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5951/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2089964134501/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-280485363/2500000000 : ℝ)*X 0 0+(44762239/80000000 : ℝ)*X 0 1+(624349593/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358233283/10000000000 : ℝ)*X 1 0+(-721153977/5000000000 : ℝ)*X 1 1+(2497398957/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358237069/10000000000 : ℝ)*X 2 0+(49947953/100000000 : ℝ)*X 2 1+(-1442306367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3960135617/10000000000 : ℝ)*X 0 0+(1497302929/5000000000 : ℝ)*X 0 1+(1012881483/2000000000 : ℝ)*X 0 2+(3960135617/10000000000 : ℝ)*X 1 0+(1497302929/5000000000 : ℝ)*X 1 1+(1012881483/2000000000 : ℝ)*X 1 2+(3960135617/10000000000 : ℝ)*X 2 0+(1497302929/5000000000 : ℝ)*X 2 1+(1012881483/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1123077299/10000000000 : ℝ)*X 0 0+(500980729/1000000000 : ℝ)*X 0 1+(1394948727/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5198931223/10000000000 : ℝ)*X 1 0+(-857309373/10000000000 : ℝ)*X 1 1+(1394948719/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2599465721/5000000000 : ℝ)*X 2 0+(223191797/400000000 : ℝ)*X 2 1+(-428654491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3964056461/10000000000 : ℝ)*X 0 0+(1002533029/2000000000 : ℝ)*X 0 1+(3047983833/10000000000 : ℝ)*X 0 2+(3964056461/10000000000 : ℝ)*X 1 0+(1002533029/2000000000 : ℝ)*X 1 1+(3047983833/10000000000 : ℝ)*X 1 2+(3964056461/10000000000 : ℝ)*X 2 0+(1002533029/2000000000 : ℝ)*X 2 1+(3047983833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13119240200938087574337/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1140929117/100000000000000 : ℝ)*(base19) + (1860390623/100000000000000 : ℝ)*(base23) + (6985247/10000000000000 : ℝ)*(base24) + (51891189/25000000000000 : ℝ)*(upper4) + (234334631/50000000000000 : ℝ)*(upper5) + (214848594767279/20000000000000 : ℝ)*(major0) + (214848594767279/20000000000000 : ℝ)*(major1) + (214848594767279/20000000000000 : ℝ)*(major2) + (832664252451021/50000000000000 : ℝ)*(sp0) + (83267022818689/5000000000000 : ℝ)*(sp1) + (416334916764951/25000000000000 : ℝ)*(sp2) + (483141436899259/100000000000000 : ℝ)*(sp3) + (6546200427/50000000000000 : ℝ)*(sp4) + (1347408313/50000000000000 : ℝ)*(sp7) + (96628826343177/20000000000000 : ℝ)*(f.failure) + (1665341597302897/100000000000000 : ℝ)*(f.sum) + (12241950797221/10000000000000000000000000000 : ℝ)*base66 + (9555058247221/20000000000000000000000000000 : ℝ)*base68 + (54336437332779/20000000000000000000000000000 : ℝ)*base69 + (19604212787221/20000000000000000000000000000 : ℝ)*base72 + (35496388927221/10000000000000000000000000000 : ℝ)*base74 + (111337407467221/20000000000000000000000000000 : ℝ)*base76 + (70567307507221/20000000000000000000000000000 : ℝ)*base78 + (157908874047221/20000000000000000000000000000 : ℝ)*base80 + (1229658957221/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5224027/500000000000000000000 : ℝ)*base89 + (5224027/500000000000000000000 : ℝ)*base91 + (5224027/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (138863772888145275649659/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (572404711/100000000000000 : ℝ)*(base19) + (701232333/100000000000000 : ℝ)*(base23) + (170083339/100000000000000 : ℝ)*(base32) + (28387929/20000000000000 : ℝ)*(upper3) + (34392643/100000000000000 : ℝ)*(upper5) + (1131705594363053/100000000000000 : ℝ)*(major0) + (1131705594363053/100000000000000 : ℝ)*(major1) + (1131705594363053/100000000000000 : ℝ)*(major2) + (180275851/10000000000000 : ℝ)*(sp1) + (898792219/25000000000000 : ℝ)*(sp2) + (1754422878854477/100000000000000 : ℝ)*(sp4) + (219302562961407/12500000000000 : ℝ)*(sp5) + (438604645613317/25000000000000 : ℝ)*(sp6) + (50898795463659/10000000000000 : ℝ)*(sp7) + (508988124719929/100000000000000 : ℝ)*(f.failure) + (1754422878854477/100000000000000 : ℝ)*(f.sum) + (44817001358447/50000000000000000000000000000 : ℝ)*base66 + (237991771008447/100000000000000000000000000000 : ℝ)*base68 + (583062258391553/100000000000000000000000000000 : ℝ)*base69 + (261799276191553/100000000000000000000000000000 : ℝ)*base71 + (224828709108447/50000000000000000000000000000 : ℝ)*base74 + (295967330391553/100000000000000000000000000000 : ℝ)*base75 + (448285027991553/100000000000000000000000000000 : ℝ)*base77 + (4332808008447/100000000000000000000000000000 : ℝ)*base80 + (40330623108447/50000000000000000000000000000 : ℝ)*base82 + (9110379/2500000000000000000000 : ℝ)*base89 + (9110379/2500000000000000000000 : ℝ)*base91 + (9110379/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1762_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (55586051/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20193/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1762_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1762_s1_0 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1157814673/10000000000 : ℝ)*x 0 + (342704999/625000000 : ℝ)*x 1 + (2541324607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1157814673/10000000000 : ℝ)^5967 ≤ (1481463554867/20000000000000 : ℝ)^4943 := by
    have hnat : (1157814673 : ℕ)^5967*20000000000000^4943 ≤ 1481463554867^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157814673 10000000000 1481463554867 20000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342704999/625000000 : ℝ)^5967 ≤ (12103740833953/25000000000000 : ℝ)^4943 := by
    have hnat : (342704999 : ℕ)^5967*25000000000000^4943 ≤ 12103740833953^4943*625000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342704999 625000000 12103740833953 25000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541324607/5000000000 : ℝ)^5967 ≤ (22088859442787/50000000000000 : ℝ)^4943 := by
    have hnat : (2541324607 : ℕ)^5967*50000000000000^4943 ≤ 22088859442787^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541324607 5000000000 22088859442787 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1157814673/10000000000 : ℝ), (342704999/625000000 : ℝ), (2541324607/5000000000 : ℝ)] ![(1481463554867/20000000000000 : ℝ), (12103740833953/25000000000000 : ℝ), (22088859442787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1157814673/10000000000 : ℝ)|^5967 ≤ (1481463554867/20000000000000 : ℝ)^4943
        have hw : |(-1157814673/10000000000 : ℝ)|=(1157814673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342704999/625000000 : ℝ)|^5967 ≤ (12103740833953/25000000000000 : ℝ)^4943
        have hw : |(342704999/625000000 : ℝ)|=(342704999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541324607/5000000000 : ℝ)|^5967 ≤ (22088859442787/50000000000000 : ℝ)^4943
        have hw : |(2541324607/5000000000 : ℝ)|=(2541324607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s1_1 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2664254249/5000000000 : ℝ)*x 0 + (-341761393/2500000000 : ℝ)*x 1 + (2541324651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2664254249/5000000000 : ℝ)^5967 ≤ (2923134913097/6250000000000 : ℝ)^4943 := by
    have hnat : (2664254249 : ℕ)^5967*6250000000000^4943 ≤ 2923134913097^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2664254249 5000000000 2923134913097 6250000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341761393/2500000000 : ℝ)^5967 ≤ (2263030390733/25000000000000 : ℝ)^4943 := by
    have hnat : (341761393 : ℕ)^5967*25000000000000^4943 ≤ 2263030390733^4943*2500000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341761393 2500000000 2263030390733 25000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541324651/5000000000 : ℝ)^5967 ≤ (44177719808913/100000000000000 : ℝ)^4943 := by
    have hnat : (2541324651 : ℕ)^5967*100000000000000^4943 ≤ 44177719808913^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541324651 5000000000 44177719808913 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2664254249/5000000000 : ℝ), (-341761393/2500000000 : ℝ), (2541324651/5000000000 : ℝ)] ![(2923134913097/6250000000000 : ℝ), (2263030390733/25000000000000 : ℝ), (44177719808913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2664254249/5000000000 : ℝ)|^5967 ≤ (2923134913097/6250000000000 : ℝ)^4943
        have hw : |(2664254249/5000000000 : ℝ)|=(2664254249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-341761393/2500000000 : ℝ)|^5967 ≤ (2263030390733/25000000000000 : ℝ)^4943
        have hw : |(-341761393/2500000000 : ℝ)|=(341761393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541324651/5000000000 : ℝ)|^5967 ≤ (44177719808913/100000000000000 : ℝ)^4943
        have hw : |(2541324651/5000000000 : ℝ)|=(2541324651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s1_2 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1065701383/2000000000 : ℝ)*x 0 + (635331397/1250000000 : ℝ)*x 1 + (-1367045211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065701383/2000000000 : ℝ)^5967 ≤ (233850709183/500000000000 : ℝ)^4943 := by
    have hnat : (1065701383 : ℕ)^5967*500000000000^4943 ≤ 233850709183^4943*2000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065701383 2000000000 233850709183 500000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635331397/1250000000 : ℝ)^5967 ≤ (44177739471841/100000000000000 : ℝ)^4943 := by
    have hnat : (635331397 : ℕ)^5967*100000000000000^4943 ≤ 44177739471841^4943*1250000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635331397 1250000000 44177739471841 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367045211/10000000000 : ℝ)^5967 ≤ (4526059338653/50000000000000 : ℝ)^4943 := by
    have hnat : (1367045211 : ℕ)^5967*50000000000000^4943 ≤ 4526059338653^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367045211 10000000000 4526059338653 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065701383/2000000000 : ℝ), (635331397/1250000000 : ℝ), (-1367045211/10000000000 : ℝ)] ![(233850709183/500000000000 : ℝ), (44177739471841/100000000000000 : ℝ), (4526059338653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065701383/2000000000 : ℝ)|^5967 ≤ (233850709183/500000000000 : ℝ)^4943
        have hw : |(1065701383/2000000000 : ℝ)|=(1065701383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635331397/1250000000 : ℝ)|^5967 ≤ (44177739471841/100000000000000 : ℝ)^4943
        have hw : |(635331397/1250000000 : ℝ)|=(635331397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1367045211/10000000000 : ℝ)|^5967 ≤ (4526059338653/50000000000000 : ℝ)^4943
        have hw : |(-1367045211/10000000000 : ℝ)|=(1367045211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s1_3 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1998112613/5000000000 : ℝ)*x 0 + (83412377/250000000 : ℝ)*x 1 + (471741871/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998112613/5000000000 : ℝ)^5967 ≤ (16523312323953/50000000000000 : ℝ)^4943 := by
    have hnat : (1998112613 : ℕ)^5967*50000000000000^4943 ≤ 16523312323953^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998112613 5000000000 16523312323953 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83412377/250000000 : ℝ)^5967 ≤ (3322343835163/12500000000000 : ℝ)^4943 := by
    have hnat : (83412377 : ℕ)^5967*12500000000000^4943 ≤ 3322343835163^4943*250000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83412377 250000000 3322343835163 12500000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471741871/1000000000 : ℝ)^5967 ≤ (10093656163373/25000000000000 : ℝ)^4943 := by
    have hnat : (471741871 : ℕ)^5967*25000000000000^4943 ≤ 10093656163373^4943*1000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471741871 1000000000 10093656163373 25000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1998112613/5000000000 : ℝ), (83412377/250000000 : ℝ), (471741871/1000000000 : ℝ)] ![(16523312323953/50000000000000 : ℝ), (3322343835163/12500000000000 : ℝ), (10093656163373/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1998112613/5000000000 : ℝ)|^5967 ≤ (16523312323953/50000000000000 : ℝ)^4943
        have hw : |(1998112613/5000000000 : ℝ)|=(1998112613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(83412377/250000000 : ℝ)|^5967 ≤ (3322343835163/12500000000000 : ℝ)^4943
        have hw : |(83412377/250000000 : ℝ)|=(83412377/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(471741871/1000000000 : ℝ)|^5967 ≤ (10093656163373/25000000000000 : ℝ)^4943
        have hw : |(471741871/1000000000 : ℝ)|=(471741871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s1_4 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1158151599/10000000000 : ℝ)*x 0 + (2544674463/5000000000 : ℝ)*x 1 + (5476438831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1158151599/10000000000 : ℝ)^5967 ≤ (7409919940167/100000000000000 : ℝ)^4943 := by
    have hnat : (1158151599 : ℕ)^5967*100000000000000^4943 ≤ 7409919940167^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158151599 10000000000 7409919940167 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544674463/5000000000 : ℝ)^5967 ≤ (11062006285889/25000000000000 : ℝ)^4943 := by
    have hnat : (2544674463 : ℕ)^5967*25000000000000^4943 ≤ 11062006285889^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544674463 5000000000 11062006285889 25000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476438831/10000000000 : ℝ)^5967 ≤ (9668410980391/20000000000000 : ℝ)^4943 := by
    have hnat : (5476438831 : ℕ)^5967*20000000000000^4943 ≤ 9668410980391^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476438831 10000000000 9668410980391 20000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1158151599/10000000000 : ℝ), (2544674463/5000000000 : ℝ), (5476438831/10000000000 : ℝ)] ![(7409919940167/100000000000000 : ℝ), (11062006285889/25000000000000 : ℝ), (9668410980391/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1158151599/10000000000 : ℝ)|^5967 ≤ (7409919940167/100000000000000 : ℝ)^4943
        have hw : |(-1158151599/10000000000 : ℝ)|=(1158151599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2544674463/5000000000 : ℝ)|^5967 ≤ (11062006285889/25000000000000 : ℝ)^4943
        have hw : |(2544674463/5000000000 : ℝ)|=(2544674463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476438831/10000000000 : ℝ)|^5967 ≤ (9668410980391/20000000000000 : ℝ)^4943
        have hw : |(5476438831/10000000000 : ℝ)|=(5476438831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s1_5 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (652837411/1250000000 : ℝ)*x 0 + (-486628933/5000000000 : ℝ)*x 1 + (5476439229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (652837411/1250000000 : ℝ)^5967 ≤ (45651356820357/100000000000000 : ℝ)^4943 := by
    have hnat : (652837411 : ℕ)^5967*100000000000000^4943 ≤ 45651356820357^4943*1250000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652837411 1250000000 45651356820357 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486628933/5000000000 : ℝ)^5967 ≤ (6006584025797/100000000000000 : ℝ)^4943 := by
    have hnat : (486628933 : ℕ)^5967*100000000000000^4943 ≤ 6006584025797^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486628933 5000000000 6006584025797 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476439229/10000000000 : ℝ)^5967 ≤ (3021378696439/6250000000000 : ℝ)^4943 := by
    have hnat : (5476439229 : ℕ)^5967*6250000000000^4943 ≤ 3021378696439^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476439229 10000000000 3021378696439 6250000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(652837411/1250000000 : ℝ), (-486628933/5000000000 : ℝ), (5476439229/10000000000 : ℝ)] ![(45651356820357/100000000000000 : ℝ), (6006584025797/100000000000000 : ℝ), (3021378696439/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(652837411/1250000000 : ℝ)|^5967 ≤ (45651356820357/100000000000000 : ℝ)^4943
        have hw : |(652837411/1250000000 : ℝ)|=(652837411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486628933/5000000000 : ℝ)|^5967 ≤ (6006584025797/100000000000000 : ℝ)^4943
        have hw : |(-486628933/5000000000 : ℝ)|=(486628933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476439229/10000000000 : ℝ)|^5967 ≤ (3021378696439/6250000000000 : ℝ)^4943
        have hw : |(5476439229/10000000000 : ℝ)|=(5476439229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s1_6 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2611350057/5000000000 : ℝ)*x 0 + (6845549/12500000 : ℝ)*x 1 + (-973256737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2611350057/5000000000 : ℝ)^5967 ≤ (22825682768047/50000000000000 : ℝ)^4943 := by
    have hnat : (2611350057 : ℕ)^5967*50000000000000^4943 ≤ 22825682768047^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611350057 5000000000 22825682768047 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6845549/12500000 : ℝ)^5967 ≤ (24171029417001/50000000000000 : ℝ)^4943 := by
    have hnat : (6845549 : ℕ)^5967*50000000000000^4943 ≤ 24171029417001^4943*12500000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6845549 12500000 24171029417001 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973256737/10000000000 : ℝ)^5967 ≤ (3003287807289/50000000000000 : ℝ)^4943 := by
    have hnat : (973256737 : ℕ)^5967*50000000000000^4943 ≤ 3003287807289^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973256737 10000000000 3003287807289 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2611350057/5000000000 : ℝ), (6845549/12500000 : ℝ), (-973256737/10000000000 : ℝ)] ![(22825682768047/50000000000000 : ℝ), (24171029417001/50000000000000 : ℝ), (3003287807289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2611350057/5000000000 : ℝ)|^5967 ≤ (22825682768047/50000000000000 : ℝ)^4943
        have hw : |(2611350057/5000000000 : ℝ)|=(2611350057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6845549/12500000 : ℝ)|^5967 ≤ (24171029417001/50000000000000 : ℝ)^4943
        have hw : |(6845549/12500000 : ℝ)|=(6845549/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-973256737/10000000000 : ℝ)|^5967 ≤ (3003287807289/50000000000000 : ℝ)^4943
        have hw : |(-973256737/10000000000 : ℝ)|=(973256737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s1_7 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (31979069/80000000 : ℝ)*x 0 + (938864319/2000000000 : ℝ)*x 1 + (336007789/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31979069/80000000 : ℝ)^5967 ≤ (16529094399943/50000000000000 : ℝ)^4943 := by
    have hnat : (31979069 : ℕ)^5967*50000000000000^4943 ≤ 16529094399943^4943*80000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31979069 80000000 16529094399943 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (938864319/2000000000 : ℝ)^5967 ≤ (40136114624817/100000000000000 : ℝ)^4943 := by
    have hnat : (938864319 : ℕ)^5967*100000000000000^4943 ≤ 40136114624817^4943*2000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938864319 2000000000 40136114624817 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336007789/1000000000 : ℝ)^5967 ≤ (26805696561471/100000000000000 : ℝ)^4943 := by
    have hnat : (336007789 : ℕ)^5967*100000000000000^4943 ≤ 26805696561471^4943*1000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336007789 1000000000 26805696561471 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31979069/80000000 : ℝ), (938864319/2000000000 : ℝ), (336007789/1000000000 : ℝ)] ![(16529094399943/50000000000000 : ℝ), (40136114624817/100000000000000 : ℝ), (26805696561471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31979069/80000000 : ℝ)|^5967 ≤ (16529094399943/50000000000000 : ℝ)^4943
        have hw : |(31979069/80000000 : ℝ)|=(31979069/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(938864319/2000000000 : ℝ)|^5967 ≤ (40136114624817/100000000000000 : ℝ)^4943
        have hw : |(938864319/2000000000 : ℝ)|=(938864319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336007789/1000000000 : ℝ)|^5967 ≤ (26805696561471/100000000000000 : ℝ)^4943
        have hw : |(336007789/1000000000 : ℝ)|=(336007789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1762_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (55586051/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20193/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1793/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (4571/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3557/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20193/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1793/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20193/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1793/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20193/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1793/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20193/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1793/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20193/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1793/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20193/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1793/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (1793/25000 : ℝ) ^ (5951/1024 : ℝ) ≤ (4472565064041/20000000000000000000 : ℝ) := by
    have hpowers : (1793/25000 : ℝ)^5951 ≤ (4472565064041/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1793 : ℕ)^5951*20000000000000000000^1024 ≤ 4472565064041^1024*25000^5951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1793 25000 4472565064041 20000000000000000000 5951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1793/25000 : ℝ)) (X := (4472565064041/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20193/100000 : ℝ) ^ (5951/1024 : ℝ) ≤ (1833109565437601/20000000000000000000 : ℝ) := by
    have hpowers : (20193/100000 : ℝ)^5951 ≤ (1833109565437601/20000000000000000000 : ℝ)^1024 := by
      have hnat : (20193 : ℕ)^5951*20000000000000000000^1024 ≤ 1833109565437601^1024*100000^5951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20193 100000 1833109565437601 20000000000000000000 5951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20193/100000 : ℝ)) (X := (1833109565437601/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000004472565064041/10000000000000000000 : ℝ) ≤ (10000000769602719/10000000000000000 : ℝ) ^ (5951/1024 : ℝ) := by
    have hpowers : (10000004472565064041/10000000000000000000 : ℝ)^1024 ≤ (10000000769602719/10000000000000000 : ℝ)^5951 := by
      have hnat : (10000004472565064041 : ℕ)^1024*10000000000000000^5951 ≤ 10000000769602719^5951*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000004472565064041 10000000000000000000 10000000769602719 10000000000000000 1024 5951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000769602719/10000000000000000 : ℝ)) (X := (10000004472565064041/10000000000000000000 : ℝ)) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10000918791065250821/10000000000000000000 : ℝ) ≤ (10000158092130437/10000000000000000 : ℝ) ^ (5951/1024 : ℝ) := by
    have hpowers : (10000918791065250821/10000000000000000000 : ℝ)^1024 ≤ (10000158092130437/10000000000000000 : ℝ)^5951 := by
      have hnat : (10000918791065250821 : ℕ)^1024*10000000000000000^5951 ≤ 10000158092130437^5951*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000918791065250821 10000000000000000000 10000158092130437 10000000000000000 1024 5951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000158092130437/10000000000000000 : ℝ)) (X := (10000918791065250821/10000000000000000000 : ℝ)) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10001833109565437601/10000000000000000000 : ℝ) ≤ (2000063082931631/2000000000000000 : ℝ) ^ (5951/1024 : ℝ) := by
    have hpowers : (10001833109565437601/10000000000000000000 : ℝ)^1024 ≤ (2000063082931631/2000000000000000 : ℝ)^5951 := by
      have hnat : (10001833109565437601 : ℕ)^1024*2000000000000000^5951 ≤ 2000063082931631^5951*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001833109565437601 10000000000000000000 2000063082931631 2000000000000000 1024 5951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000063082931631/2000000000000000 : ℝ)) (X := (10001833109565437601/10000000000000000000 : ℝ)) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4472565064041/20000000000000000000 : ℝ) ≤ ((130207753386659417107/130210000000000000000 : ℝ)+2*(78661263859/651050000000000 : ℝ)*(1793/25000 : ℝ))^(5951/1024 : ℝ) := by
    rw [show (130207753386659417107/130210000000000000000 : ℝ)+2*(78661263859/651050000000000 : ℝ)*(1793/25000 : ℝ)=(10000000769602719/10000000000000000 : ℝ) by norm_num, show 1+2*(4472565064041/20000000000000000000 : ℝ)=(10000004472565064041/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1833109565437601/20000000000000000000 : ℝ)+(4472565064041/20000000000000000000 : ℝ) ≤ ((130207753386659417107/130210000000000000000 : ℝ)+(78661263859/651050000000000 : ℝ)*((20193/100000 : ℝ)+(1793/25000 : ℝ)))^(5951/1024 : ℝ) := by
    rw [show (130207753386659417107/130210000000000000000 : ℝ)+(78661263859/651050000000000 : ℝ)*((20193/100000 : ℝ)+(1793/25000 : ℝ))=(10000158092130437/10000000000000000 : ℝ) by norm_num, show 1+(1833109565437601/20000000000000000000 : ℝ)+(4472565064041/20000000000000000000 : ℝ)=(10000918791065250821/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1833109565437601/20000000000000000000 : ℝ) ≤ ((130207753386659417107/130210000000000000000 : ℝ)+2*(78661263859/651050000000000 : ℝ)*(20193/100000 : ℝ))^(5951/1024 : ℝ) := by
    rw [show (130207753386659417107/130210000000000000000 : ℝ)+2*(78661263859/651050000000000 : ℝ)*(20193/100000 : ℝ)=(2000063082931631/2000000000000000 : ℝ) by norm_num, show 1+2*(1833109565437601/20000000000000000000 : ℝ)=(10001833109565437601/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (130207753386659417107/130210000000000000000 : ℝ)*(X 1 0+X 2 0)+(78661263859/651050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5951/1024 : ℝ)) (lo := (1793/25000 : ℝ)) (hi := (20193/100000 : ℝ)) (c := (130207753386659417107/130210000000000000000 : ℝ)) (alpha := (78661263859/651050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (130207753386659417107/130210000000000000000 : ℝ)*(X 0 1+X 2 1)+(78661263859/651050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5951/1024 : ℝ)) (lo := (1793/25000 : ℝ)) (hi := (20193/100000 : ℝ)) (c := (130207753386659417107/130210000000000000000 : ℝ)) (alpha := (78661263859/651050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (130207753386659417107/130210000000000000000 : ℝ)*(X 0 2+X 1 2)+(78661263859/651050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5951/1024 : ℝ)) (lo := (1793/25000 : ℝ)) (hi := (20193/100000 : ℝ)) (c := (130207753386659417107/130210000000000000000 : ℝ)) (alpha := (78661263859/651050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1157814673/10000000000 : ℝ)*X 0 0+(342704999/625000000 : ℝ)*X 0 1+(2541324607/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2664254249/5000000000 : ℝ)*X 1 0+(-341761393/2500000000 : ℝ)*X 1 1+(2541324651/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1065701383/2000000000 : ℝ)*X 2 0+(635331397/1250000000 : ℝ)*X 2 1+(-1367045211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1998112613/5000000000 : ℝ)*X 0 0+(83412377/250000000 : ℝ)*X 0 1+(471741871/1000000000 : ℝ)*X 0 2+(1998112613/5000000000 : ℝ)*X 1 0+(83412377/250000000 : ℝ)*X 1 1+(471741871/1000000000 : ℝ)*X 1 2+(1998112613/5000000000 : ℝ)*X 2 0+(83412377/250000000 : ℝ)*X 2 1+(471741871/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1158151599/10000000000 : ℝ)*X 0 0+(2544674463/5000000000 : ℝ)*X 0 1+(5476438831/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((652837411/1250000000 : ℝ)*X 1 0+(-486628933/5000000000 : ℝ)*X 1 1+(5476439229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2611350057/5000000000 : ℝ)*X 2 0+(6845549/12500000 : ℝ)*X 2 1+(-973256737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((31979069/80000000 : ℝ)*X 0 0+(938864319/2000000000 : ℝ)*X 0 1+(336007789/1000000000 : ℝ)*X 0 2+(31979069/80000000 : ℝ)*X 1 0+(938864319/2000000000 : ℝ)*X 1 1+(336007789/1000000000 : ℝ)*X 1 2+(31979069/80000000 : ℝ)*X 2 0+(938864319/2000000000 : ℝ)*X 2 1+(336007789/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15582561707808448267267083363/1627625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1008136599/100000000000000 : ℝ)*(base19) + (259612221/100000000000000 : ℝ)*(base23) + (65387293/50000000000000 : ℝ)*(upper3) + (1860981/50000000000000 : ℝ)*(upper4) + (30165109/12500000000000 : ℝ)*(upper5) + (805059922406403/50000000000000 : ℝ)*(major0) + (805059922406403/50000000000000 : ℝ)*(major1) + (805059922406403/50000000000000 : ℝ)*(major2) + (2496073117100547/100000000000000 : ℝ)*(sp0) + (1248040967347213/50000000000000 : ℝ)*(sp1) + (624020670804701/25000000000000 : ℝ)*(sp2) + (724155140403161/100000000000000 : ℝ)*(sp3) + (9825730477/100000000000000 : ℝ)*(sp4) + (1287264639/100000000000000 : ℝ)*(sp7) + (3620782138339/500000000000 : ℝ)*(f.failure) + (156005183926939/6250000000000 : ℝ)*(f.sum) + (182933714123527/65105000000000000000000000000 : ℝ)*base66 + (976713714712436121/6510500000000000000000000000000000 : ℝ)*base67 + (17876720509802563879/6510500000000000000000000000000000 : ℝ)*base70 + (46328656590964563879/6510500000000000000000000000000000 : ℝ)*base72 + (336006619243343/65105000000000000000000000000 : ℝ)*base73 + (93012566396476063879/6510500000000000000000000000000000 : ℝ)*base76 + (56731117292840563879/6510500000000000000000000000000000 : ℝ)*base78 + (76172350304104563879/6510500000000000000000000000000000 : ℝ)*base80 + (24434144911807/16276250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (40711/12500000000000000000 : ℝ)*base90 + (40711/12500000000000000000 : ℝ)*base92 + (40711/12500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3667045514404339366877999349/1627625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (278466531/50000000000000 : ℝ)*(base15) + (830327/3125000000000 : ℝ)*(base29) + (132617969/100000000000000 : ℝ)*(upper2) + (2423857/2000000000000 : ℝ)*(upper4) + (282701963/100000000000000 : ℝ)*(upper5) + (83322018938623/5000000000000 : ℝ)*(major0) + (416610101335731/25000000000000 : ℝ)*(major1) + (416610101335731/25000000000000 : ℝ)*(major2) + (2751848457/50000000000000 : ℝ)*(sp0) + (389863539/10000000000000 : ℝ)*(sp2) + (1291694228133193/50000000000000 : ℝ)*(sp4) + (1291696688229887/50000000000000 : ℝ)*(sp5) + (1291695017378723/50000000000000 : ℝ)*(sp6) + (149897355124483/20000000000000 : ℝ)*(sp7) + (149897355124483/20000000000000 : ℝ)*(f.failure) + (25833939599633/1000000000000 : ℝ)*(f.sum) + (21668656191663/65105000000000000000000000000 : ℝ)*base66 + (13430805915138300217/3255250000000000000000000000000000 : ℝ)*base67 + (1226411501019550217/3255250000000000000000000000000000 : ℝ)*base69 + (2340368758225033661/651050000000000000000000000000000 : ℝ)*base71 + (16383839129551/65105000000000000000000000000 : ℝ)*base73 + (4890359977099750217/3255250000000000000000000000000000 : ℝ)*base75 + (416717171346066339/651050000000000000000000000000000 : ℝ)*base78 + (7579770891787499783/3255250000000000000000000000000000 : ℝ)*base80 + (50155302432867/32552500000000000000000000000 : ℝ)*base82 + (3386633/500000000000000000000 : ℝ)*base89 + (3386633/500000000000000000000 : ℝ)*base91 + (3386633/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1762_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (55586051/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20193/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1793/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3557/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1762_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1762_s2_0 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1158414983/10000000000 : ℝ)*x 0 + (5481345979/10000000000 : ℝ)*x 1 + (5084171853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1158414983/10000000000 : ℝ)^5967 ≤ (1852988557877/25000000000000 : ℝ)^4943 := by
    have hnat : (1158414983 : ℕ)^5967*25000000000000^4943 ≤ 1852988557877^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158414983 10000000000 1852988557877 25000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5481345979/10000000000 : ℝ)^5967 ≤ (9678870018431/20000000000000 : ℝ)^4943 := by
    have hnat : (5481345979 : ℕ)^5967*20000000000000^4943 ≤ 9678870018431^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481345979 10000000000 9678870018431 20000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084171853/10000000000 : ℝ)^5967 ≤ (44193695656259/100000000000000 : ℝ)^4943 := by
    have hnat : (5084171853 : ℕ)^5967*100000000000000^4943 ≤ 44193695656259^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084171853 10000000000 44193695656259 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1158414983/10000000000 : ℝ), (5481345979/10000000000 : ℝ), (5084171853/10000000000 : ℝ)] ![(1852988557877/25000000000000 : ℝ), (9678870018431/20000000000000 : ℝ), (44193695656259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1158414983/10000000000 : ℝ)|^5967 ≤ (1852988557877/25000000000000 : ℝ)^4943
        have hw : |(-1158414983/10000000000 : ℝ)|=(1158414983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5481345979/10000000000 : ℝ)|^5967 ≤ (9678870018431/20000000000000 : ℝ)^4943
        have hw : |(5481345979/10000000000 : ℝ)|=(5481345979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084171853/10000000000 : ℝ)|^5967 ≤ (44193695656259/100000000000000 : ℝ)^4943
        have hw : |(5084171853/10000000000 : ℝ)|=(5084171853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s2_1 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5327967507/10000000000 : ℝ)*x 0 + (-682881961/5000000000 : ℝ)*x 1 + (317760741/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5327967507/10000000000 : ℝ)^5967 ≤ (5845553313163/12500000000000 : ℝ)^4943 := by
    have hnat : (5327967507 : ℕ)^5967*12500000000000^4943 ≤ 5845553313163^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5327967507 10000000000 5845553313163 12500000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682881961/5000000000 : ℝ)^5967 ≤ (141279340423/1562500000000 : ℝ)^4943 := by
    have hnat : (682881961 : ℕ)^5967*1562500000000^4943 ≤ 141279340423^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682881961 5000000000 141279340423 1562500000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317760741/625000000 : ℝ)^5967 ≤ (44193695687739/100000000000000 : ℝ)^4943 := by
    have hnat : (317760741 : ℕ)^5967*100000000000000^4943 ≤ 44193695687739^4943*625000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317760741 625000000 44193695687739 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5327967507/10000000000 : ℝ), (-682881961/5000000000 : ℝ), (317760741/625000000 : ℝ)] ![(5845553313163/12500000000000 : ℝ), (141279340423/1562500000000 : ℝ), (44193695687739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5327967507/10000000000 : ℝ)|^5967 ≤ (5845553313163/12500000000000 : ℝ)^4943
        have hw : |(5327967507/10000000000 : ℝ)|=(5327967507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-682881961/5000000000 : ℝ)|^5967 ≤ (141279340423/1562500000000 : ℝ)^4943
        have hw : |(-682881961/5000000000 : ℝ)|=(682881961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317760741/625000000 : ℝ)|^5967 ≤ (44193695687739/100000000000000 : ℝ)^4943
        have hw : |(317760741/625000000 : ℝ)|=(317760741/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s2_2 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1065593499/2000000000 : ℝ)*x 0 + (5084171849/10000000000 : ℝ)*x 1 + (-1365763949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065593499/2000000000 : ℝ)^5967 ≤ (23382213189079/50000000000000 : ℝ)^4943 := by
    have hnat : (1065593499 : ℕ)^5967*50000000000000^4943 ≤ 23382213189079^4943*2000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065593499 2000000000 23382213189079 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5084171849/10000000000 : ℝ)^5967 ≤ (44193695614287/100000000000000 : ℝ)^4943 := by
    have hnat : (5084171849 : ℕ)^5967*100000000000000^4943 ≤ 44193695614287^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084171849 10000000000 44193695614287 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365763949/10000000000 : ℝ)^5967 ≤ (9041878002853/100000000000000 : ℝ)^4943 := by
    have hnat : (1365763949 : ℕ)^5967*100000000000000^4943 ≤ 9041878002853^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365763949 10000000000 9041878002853 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065593499/2000000000 : ℝ), (5084171849/10000000000 : ℝ), (-1365763949/10000000000 : ℝ)] ![(23382213189079/50000000000000 : ℝ), (44193695614287/100000000000000 : ℝ), (9041878002853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065593499/2000000000 : ℝ)|^5967 ≤ (23382213189079/50000000000000 : ℝ)^4943
        have hw : |(1065593499/2000000000 : ℝ)|=(1065593499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5084171849/10000000000 : ℝ)|^5967 ≤ (44193695614287/100000000000000 : ℝ)^4943
        have hw : |(5084171849/10000000000 : ℝ)|=(5084171849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1365763949/10000000000 : ℝ)|^5967 ≤ (9041878002853/100000000000000 : ℝ)^4943
        have hw : |(-1365763949/10000000000 : ℝ)|=(1365763949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s2_3 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1998360207/5000000000 : ℝ)*x 0 + (334241509/1000000000 : ℝ)*x 1 + (4711428309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998360207/5000000000 : ℝ)^5967 ≤ (16525783981329/50000000000000 : ℝ)^4943 := by
    have hnat : (1998360207 : ℕ)^5967*50000000000000^4943 ≤ 16525783981329^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998360207 5000000000 16525783981329 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (334241509/1000000000 : ℝ)^5967 ≤ (13317844963831/50000000000000 : ℝ)^4943 := by
    have hnat : (334241509 : ℕ)^5967*50000000000000^4943 ≤ 13317844963831^4943*1000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334241509 1000000000 13317844963831 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4711428309/10000000000 : ℝ)^5967 ≤ (8062548419347/20000000000000 : ℝ)^4943 := by
    have hnat : (4711428309 : ℕ)^5967*20000000000000^4943 ≤ 8062548419347^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4711428309 10000000000 8062548419347 20000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1998360207/5000000000 : ℝ), (334241509/1000000000 : ℝ), (4711428309/10000000000 : ℝ)] ![(16525783981329/50000000000000 : ℝ), (13317844963831/50000000000000 : ℝ), (8062548419347/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1998360207/5000000000 : ℝ)|^5967 ≤ (16525783981329/50000000000000 : ℝ)^4943
        have hw : |(1998360207/5000000000 : ℝ)|=(1998360207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(334241509/1000000000 : ℝ)|^5967 ≤ (13317844963831/50000000000000 : ℝ)^4943
        have hw : |(334241509/1000000000 : ℝ)|=(334241509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4711428309/10000000000 : ℝ)|^5967 ≤ (8062548419347/20000000000000 : ℝ)^4943
        have hw : |(4711428309/10000000000 : ℝ)|=(4711428309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s2_4 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-579371229/5000000000 : ℝ)*x 0 + (5090757581/10000000000 : ℝ)*x 1 + (5474623023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (579371229/5000000000 : ℝ)^5967 ≤ (231702614821/3125000000000 : ℝ)^4943 := by
    have hnat : (579371229 : ℕ)^5967*3125000000000^4943 ≤ 231702614821^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579371229 5000000000 231702614821 3125000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5090757581/10000000000 : ℝ)^5967 ≤ (22131404950153/50000000000000 : ℝ)^4943 := by
    have hnat : (5090757581 : ℕ)^5967*50000000000000^4943 ≤ 22131404950153^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5090757581 10000000000 22131404950153 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474623023/10000000000 : ℝ)^5967 ≤ (48322706401963/100000000000000 : ℝ)^4943 := by
    have hnat : (5474623023 : ℕ)^5967*100000000000000^4943 ≤ 48322706401963^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474623023 10000000000 48322706401963 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-579371229/5000000000 : ℝ), (5090757581/10000000000 : ℝ), (5474623023/10000000000 : ℝ)] ![(231702614821/3125000000000 : ℝ), (22131404950153/50000000000000 : ℝ), (48322706401963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-579371229/5000000000 : ℝ)|^5967 ≤ (231702614821/3125000000000 : ℝ)^4943
        have hw : |(-579371229/5000000000 : ℝ)|=(579371229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5090757581/10000000000 : ℝ)|^5967 ≤ (22131404950153/50000000000000 : ℝ)^4943
        have hw : |(5090757581/10000000000 : ℝ)|=(5090757581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474623023/10000000000 : ℝ)|^5967 ≤ (48322706401963/100000000000000 : ℝ)^4943
        have hw : |(5474623023/10000000000 : ℝ)|=(5474623023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s2_5 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5223082167/10000000000 : ℝ)*x 0 + (-975312779/10000000000 : ℝ)*x 1 + (2737311507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5223082167/10000000000 : ℝ)^5967 ≤ (22827698445417/50000000000000 : ℝ)^4943 := by
    have hnat : (5223082167 : ℕ)^5967*50000000000000^4943 ≤ 22827698445417^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223082167 10000000000 22827698445417 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (975312779/10000000000 : ℝ)^5967 ≤ (3010948391869/50000000000000 : ℝ)^4943 := by
    have hnat : (975312779 : ℕ)^5967*50000000000000^4943 ≤ 3010948391869^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975312779 10000000000 3010948391869 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2737311507/5000000000 : ℝ)^5967 ≤ (24161353153033/50000000000000 : ℝ)^4943 := by
    have hnat : (2737311507 : ℕ)^5967*50000000000000^4943 ≤ 24161353153033^4943*5000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737311507 5000000000 24161353153033 50000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5223082167/10000000000 : ℝ), (-975312779/10000000000 : ℝ), (2737311507/5000000000 : ℝ)] ![(22827698445417/50000000000000 : ℝ), (3010948391869/50000000000000 : ℝ), (24161353153033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5223082167/10000000000 : ℝ)|^5967 ≤ (22827698445417/50000000000000 : ℝ)^4943
        have hw : |(5223082167/10000000000 : ℝ)|=(5223082167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-975312779/10000000000 : ℝ)|^5967 ≤ (3010948391869/50000000000000 : ℝ)^4943
        have hw : |(-975312779/10000000000 : ℝ)|=(975312779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2737311507/5000000000 : ℝ)|^5967 ≤ (24161353153033/50000000000000 : ℝ)^4943
        have hw : |(2737311507/5000000000 : ℝ)|=(2737311507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s2_6 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5223082153/10000000000 : ℝ)*x 0 + (5474623027/10000000000 : ℝ)*x 1 + (-975312781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5223082153/10000000000 : ℝ)^5967 ≤ (45655396743107/100000000000000 : ℝ)^4943 := by
    have hnat : (5223082153 : ℕ)^5967*100000000000000^4943 ≤ 45655396743107^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223082153 10000000000 45655396743107 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474623027/10000000000 : ℝ)^5967 ≤ (6040338305573/12500000000000 : ℝ)^4943 := by
    have hnat : (5474623027 : ℕ)^5967*12500000000000^4943 ≤ 6040338305573^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474623027 10000000000 6040338305573 12500000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (975312781/10000000000 : ℝ)^5967 ≤ (1204379359729/20000000000000 : ℝ)^4943 := by
    have hnat : (975312781 : ℕ)^5967*20000000000000^4943 ≤ 1204379359729^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975312781 10000000000 1204379359729 20000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5223082153/10000000000 : ℝ), (5474623027/10000000000 : ℝ), (-975312781/10000000000 : ℝ)] ![(45655396743107/100000000000000 : ℝ), (6040338305573/12500000000000 : ℝ), (1204379359729/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5223082153/10000000000 : ℝ)|^5967 ≤ (45655396743107/100000000000000 : ℝ)^4943
        have hw : |(5223082153/10000000000 : ℝ)|=(5223082153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474623027/10000000000 : ℝ)|^5967 ≤ (6040338305573/12500000000000 : ℝ)^4943
        have hw : |(5474623027/10000000000 : ℝ)|=(5474623027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-975312781/10000000000 : ℝ)|^5967 ≤ (1204379359729/20000000000000 : ℝ)^4943
        have hw : |(-975312781/10000000000 : ℝ)|=(975312781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1762_s2_7 (p : ℝ) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3997849187/10000000000 : ℝ)*x 0 + (586091003/1250000000 : ℝ)*x 1 + (3365588379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3997849187/10000000000 : ℝ)^5967 ≤ (661256732851/2000000000000 : ℝ)^4943 := by
    have hnat : (3997849187 : ℕ)^5967*2000000000000^4943 ≤ 661256732851^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3997849187 10000000000 661256732851 2000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586091003/1250000000 : ℝ)^5967 ≤ (40078389690151/100000000000000 : ℝ)^4943 := by
    have hnat : (586091003 : ℕ)^5967*100000000000000^4943 ≤ 40078389690151^4943*1250000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586091003 1250000000 40078389690151 100000000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3365588379/10000000000 : ℝ)^5967 ≤ (3357346705687/12500000000000 : ℝ)^4943 := by
    have hnat : (3365588379 : ℕ)^5967*12500000000000^4943 ≤ 3357346705687^4943*10000000000^5967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3365588379 10000000000 3357346705687 12500000000000 5967 4943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5967/1024 : ℝ)) 5967 4943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3997849187/10000000000 : ℝ), (586091003/1250000000 : ℝ), (3365588379/10000000000 : ℝ)] ![(661256732851/2000000000000 : ℝ), (40078389690151/100000000000000 : ℝ), (3357346705687/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3997849187/10000000000 : ℝ)|^5967 ≤ (661256732851/2000000000000 : ℝ)^4943
        have hw : |(3997849187/10000000000 : ℝ)|=(3997849187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(586091003/1250000000 : ℝ)|^5967 ≤ (40078389690151/100000000000000 : ℝ)^4943
        have hw : |(586091003/1250000000 : ℝ)|=(586091003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3365588379/10000000000 : ℝ)|^5967 ≤ (3357346705687/12500000000000 : ℝ)^4943
        have hw : |(3365588379/10000000000 : ℝ)|=(3365588379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1762_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (55586051/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3557/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1147/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1109/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3557/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4571/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3557/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4571/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3557/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4571/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3557/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4571/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3557/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4571/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3557/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4571/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4571/50000 : ℝ) ^ (5951/1024 : ℝ) ≤ (45818058886953/50000000000000000000 : ℝ) := by
    have hpowers : (4571/50000 : ℝ)^5951 ≤ (45818058886953/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4571 : ℕ)^5951*50000000000000000000^1024 ≤ 45818058886953^1024*50000^5951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4571 50000 45818058886953 50000000000000000000 5951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4571/50000 : ℝ)) (X := (45818058886953/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3557/20000 : ℝ) ^ (5951/1024 : ℝ) ≤ (1095495239175789/25000000000000000000 : ℝ) := by
    have hpowers : (3557/20000 : ℝ)^5951 ≤ (1095495239175789/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3557 : ℕ)^5951*25000000000000000000^1024 ≤ 1095495239175789^1024*20000^5951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3557 20000 1095495239175789 25000000000000000000 5951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3557/20000 : ℝ)) (X := (1095495239175789/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000045818058886953/25000000000000000000 : ℝ) ≤ (5000001576799083/5000000000000000 : ℝ) ^ (5951/1024 : ℝ) := by
    have hpowers : (25000045818058886953/25000000000000000000 : ℝ)^1024 ≤ (5000001576799083/5000000000000000 : ℝ)^5951 := by
      have hnat : (25000045818058886953 : ℕ)^1024*5000000000000000^5951 ≤ 5000001576799083^5951*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000045818058886953 25000000000000000000 5000001576799083 5000000000000000 1024 5951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000001576799083/5000000000000000 : ℝ)) (X := (25000045818058886953/25000000000000000000 : ℝ)) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50002236808537238531/50000000000000000000 : ℝ) ≤ (5000038488481353/5000000000000000 : ℝ) ^ (5951/1024 : ℝ) := by
    have hpowers : (50002236808537238531/50000000000000000000 : ℝ)^1024 ≤ (5000038488481353/5000000000000000 : ℝ)^5951 := by
      have hnat : (50002236808537238531 : ℕ)^1024*5000000000000000^5951 ≤ 5000038488481353^5951*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002236808537238531 50000000000000000000 5000038488481353 5000000000000000 1024 5951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000038488481353/5000000000000000 : ℝ)) (X := (50002236808537238531/50000000000000000000 : ℝ)) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12501095495239175789/12500000000000000000 : ℝ) ≤ (5000075400163623/5000000000000000 : ℝ) ^ (5951/1024 : ℝ) := by
    have hpowers : (12501095495239175789/12500000000000000000 : ℝ)^1024 ≤ (5000075400163623/5000000000000000 : ℝ)^5951 := by
      have hnat : (12501095495239175789 : ℕ)^1024*5000000000000000^5951 ≤ 5000075400163623^5951*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501095495239175789 12500000000000000000 5000075400163623 5000000000000000 1024 5951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000075400163623/5000000000000000 : ℝ)) (X := (12501095495239175789/12500000000000000000 : ℝ)) (by norm_num) 5951 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(45818058886953/50000000000000000000 : ℝ) ≤ ((14404779578358616563/14405000000000000000 : ℝ)+2*(1230389409/14405000000000 : ℝ)*(4571/50000 : ℝ))^(5951/1024 : ℝ) := by
    rw [show (14404779578358616563/14405000000000000000 : ℝ)+2*(1230389409/14405000000000 : ℝ)*(4571/50000 : ℝ)=(5000001576799083/5000000000000000 : ℝ) by norm_num, show 1+2*(45818058886953/50000000000000000000 : ℝ)=(25000045818058886953/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1095495239175789/25000000000000000000 : ℝ)+(45818058886953/50000000000000000000 : ℝ) ≤ ((14404779578358616563/14405000000000000000 : ℝ)+(1230389409/14405000000000 : ℝ)*((3557/20000 : ℝ)+(4571/50000 : ℝ)))^(5951/1024 : ℝ) := by
    rw [show (14404779578358616563/14405000000000000000 : ℝ)+(1230389409/14405000000000 : ℝ)*((3557/20000 : ℝ)+(4571/50000 : ℝ))=(5000038488481353/5000000000000000 : ℝ) by norm_num, show 1+(1095495239175789/25000000000000000000 : ℝ)+(45818058886953/50000000000000000000 : ℝ)=(50002236808537238531/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1095495239175789/25000000000000000000 : ℝ) ≤ ((14404779578358616563/14405000000000000000 : ℝ)+2*(1230389409/14405000000000 : ℝ)*(3557/20000 : ℝ))^(5951/1024 : ℝ) := by
    rw [show (14404779578358616563/14405000000000000000 : ℝ)+2*(1230389409/14405000000000 : ℝ)*(3557/20000 : ℝ)=(5000075400163623/5000000000000000 : ℝ) by norm_num, show 1+2*(1095495239175789/25000000000000000000 : ℝ)=(12501095495239175789/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14404779578358616563/14405000000000000000 : ℝ)*(X 1 0+X 2 0)+(1230389409/14405000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5951/1024 : ℝ)) (lo := (4571/50000 : ℝ)) (hi := (3557/20000 : ℝ)) (c := (14404779578358616563/14405000000000000000 : ℝ)) (alpha := (1230389409/14405000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14404779578358616563/14405000000000000000 : ℝ)*(X 0 1+X 2 1)+(1230389409/14405000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5951/1024 : ℝ)) (lo := (4571/50000 : ℝ)) (hi := (3557/20000 : ℝ)) (c := (14404779578358616563/14405000000000000000 : ℝ)) (alpha := (1230389409/14405000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14404779578358616563/14405000000000000000 : ℝ)*(X 0 2+X 1 2)+(1230389409/14405000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5951/1024 : ℝ)) (lo := (4571/50000 : ℝ)) (hi := (3557/20000 : ℝ)) (c := (14404779578358616563/14405000000000000000 : ℝ)) (alpha := (1230389409/14405000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1158414983/10000000000 : ℝ)*X 0 0+(5481345979/10000000000 : ℝ)*X 0 1+(5084171853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5327967507/10000000000 : ℝ)*X 1 0+(-682881961/5000000000 : ℝ)*X 1 1+(317760741/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1065593499/2000000000 : ℝ)*X 2 0+(5084171849/10000000000 : ℝ)*X 2 1+(-1365763949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1998360207/5000000000 : ℝ)*X 0 0+(334241509/1000000000 : ℝ)*X 0 1+(4711428309/10000000000 : ℝ)*X 0 2+(1998360207/5000000000 : ℝ)*X 1 0+(334241509/1000000000 : ℝ)*X 1 1+(4711428309/10000000000 : ℝ)*X 1 2+(1998360207/5000000000 : ℝ)*X 2 0+(334241509/1000000000 : ℝ)*X 2 1+(4711428309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-579371229/5000000000 : ℝ)*X 0 0+(5090757581/10000000000 : ℝ)*X 0 1+(5474623023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5223082167/10000000000 : ℝ)*X 1 0+(-975312779/10000000000 : ℝ)*X 1 1+(2737311507/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5223082153/10000000000 : ℝ)*X 2 0+(5474623027/10000000000 : ℝ)*X 2 1+(-975312781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3997849187/10000000000 : ℝ)*X 0 0+(586091003/1250000000 : ℝ)*X 0 1+(3365588379/10000000000 : ℝ)*X 0 2+(3997849187/10000000000 : ℝ)*X 1 0+(586091003/1250000000 : ℝ)*X 1 1+(3365588379/10000000000 : ℝ)*X 1 2+(3997849187/10000000000 : ℝ)*X 2 0+(586091003/1250000000 : ℝ)*X 2 1+(3365588379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1762_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4374736604189569382332339527/720250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103573741/12500000000000 : ℝ)*(base19) + (780603337/100000000000000 : ℝ)*(base23) + (1127287/5000000000000 : ℝ)*(lower2) + (37800671/25000000000000 : ℝ)*(upper3) + (21326687/20000000000000 : ℝ)*(upper5) + (1624129056306143/100000000000000 : ℝ)*(major0) + (1624129056306143/100000000000000 : ℝ)*(major1) + (1624129056306143/100000000000000 : ℝ)*(major2) + (2517794216986769/100000000000000 : ℝ)*(sp0) + (1258899983639521/50000000000000 : ℝ)*(sp1) + (2517800015265633/100000000000000 : ℝ)*(sp2) + (365227487821801/50000000000000 : ℝ)*(sp3) + (6578882201/100000000000000 : ℝ)*(sp4) + (1069317953/50000000000000 : ℝ)*(sp7) + (182614278569877/25000000000000 : ℝ)*(f.failure) + (251780079586897/10000000000000 : ℝ)*(f.sum) + (375531126917/2881000000000000000000000000 : ℝ)*base66 + (7942979130452553491/1440500000000000000000000000000000 : ℝ)*base68 + (438079750299446509/1440500000000000000000000000000000 : ℝ)*base69 + (7329954747366553491/1440500000000000000000000000000000 : ℝ)*base72 + (900427039813/720250000000000000000000000 : ℝ)*base74 + (3877539456933446509/1440500000000000000000000000000000 : ℝ)*base75 + (3637248901927053491/1440500000000000000000000000000000 : ℝ)*base78 + (11623021289745053491/1440500000000000000000000000000000 : ℝ)*base80 + (9126724213273/2881000000000000000000000000 : ℝ)*base81 + (3764273/625000000000000000000 : ℝ)*base90 + (3764273/625000000000000000000 : ℝ)*base92 + (3764273/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2287739655117263132692983579/360125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (809836893/100000000000000 : ℝ)*(base19) + (21398157/2500000000000 : ℝ)*(base23) + (227717251/100000000000000 : ℝ)*(lower1) + (34104977/25000000000000 : ℝ)*(upper3) + (747529/3125000000000 : ℝ)*(lower4) + (26735689/20000000000000 : ℝ)*(upper5) + (840212452294337/50000000000000 : ℝ)*(major0) + (840212452294337/50000000000000 : ℝ)*(major1) + (840212452294337/50000000000000 : ℝ)*(major2) + (90552181/25000000000000 : ℝ)*(sp2) + (325634156199939/12500000000000 : ℝ)*(sp4) + (2605072439762619/100000000000000 : ℝ)*(sp5) + (651268007866127/25000000000000 : ℝ)*(sp6) + (755776347823609/100000000000000 : ℝ)*(sp7) + (755776347823609/100000000000000 : ℝ)*(f.failure) + (325634156199939/12500000000000 : ℝ)*(f.sum) + (8961977124717/2881000000000000000000000000 : ℝ)*base65 + (8426846138699696269/720250000000000000000000000000000 : ℝ)*base68 + (8992303969354446269/720250000000000000000000000000000 : ℝ)*base70 + (9045794537701696269/720250000000000000000000000000000 : ℝ)*base72 + (15469868090951/2881000000000000000000000000 : ℝ)*base74 + (889166557376946269/720250000000000000000000000000000 : ℝ)*base76 + (6923244243204446269/720250000000000000000000000000000 : ℝ)*base78 + (2034725285079696269/720250000000000000000000000000000 : ℝ)*base80 + (8122054979883/2881000000000000000000000000 : ℝ)*base82 + (18878059/2500000000000000000000 : ℝ)*base89 + (18878059/2500000000000000000000 : ℝ)*base91 + (18878059/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1762_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (55586051/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3557/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1147/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1109/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1762_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1762_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (55586051/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1147/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1109/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1762_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1762_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1762_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (55586051/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1147/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1109/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1762_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
