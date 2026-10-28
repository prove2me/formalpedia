-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1142_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:31:50.365264+00:00
-- url     : https://prove2.me/submissions/abd5f76a-6df3-4995-b6dc-19aef9daacba

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
theorem support_rectangle_w1142_s3_0 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-540771621/2500000000 : ℝ)*x 0 + (135729377/250000000 : ℝ)*x 1 + (5232085633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540771621/2500000000 : ℝ)^8335 ≤ (13136303387081/100000000000000 : ℝ)^6287 := by
    have hnat : (540771621 : ℕ)^8335*100000000000000^6287 ≤ 13136303387081^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540771621 2500000000 13136303387081 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135729377/250000000 : ℝ)^8335 ≤ (22248103212677/50000000000000 : ℝ)^6287 := by
    have hnat : (135729377 : ℕ)^8335*50000000000000^6287 ≤ 22248103212677^6287*250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135729377 250000000 22248103212677 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232085633/10000000000 : ℝ)^8335 ≤ (10591872543101/25000000000000 : ℝ)^6287 := by
    have hnat : (5232085633 : ℕ)^8335*25000000000000^6287 ≤ 10591872543101^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232085633 10000000000 10591872543101 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540771621/2500000000 : ℝ), (135729377/250000000 : ℝ), (5232085633/10000000000 : ℝ)] ![(13136303387081/100000000000000 : ℝ), (22248103212677/50000000000000 : ℝ), (10591872543101/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540771621/2500000000 : ℝ)|^8335 ≤ (13136303387081/100000000000000 : ℝ)^6287
        have hw : |(-540771621/2500000000 : ℝ)|=(540771621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135729377/250000000 : ℝ)|^8335 ≤ (22248103212677/50000000000000 : ℝ)^6287
        have hw : |(135729377/250000000 : ℝ)|=(135729377/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232085633/10000000000 : ℝ)|^8335 ≤ (10591872543101/25000000000000 : ℝ)^6287
        have hw : |(5232085633/10000000000 : ℝ)|=(5232085633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s3_1 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676896409/5000000000 : ℝ)*x 0 + (-45276637/200000000 : ℝ)*x 1 + (163502671/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676896409/5000000000 : ℝ)^8335 ≤ (2729937226277/6250000000000 : ℝ)^6287 := by
    have hnat : (2676896409 : ℕ)^8335*6250000000000^6287 ≤ 2729937226277^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676896409 5000000000 2729937226277 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45276637/200000000 : ℝ)^8335 ≤ (697675796001/5000000000000 : ℝ)^6287 := by
    have hnat : (45276637 : ℕ)^8335*5000000000000^6287 ≤ 697675796001^6287*200000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45276637 200000000 697675796001 5000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163502671/312500000 : ℝ)^8335 ≤ (42367488443997/100000000000000 : ℝ)^6287 := by
    have hnat : (163502671 : ℕ)^8335*100000000000000^6287 ≤ 42367488443997^6287*312500000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163502671 312500000 42367488443997 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676896409/5000000000 : ℝ), (-45276637/200000000 : ℝ), (163502671/312500000 : ℝ)] ![(2729937226277/6250000000000 : ℝ), (697675796001/5000000000000 : ℝ), (42367488443997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676896409/5000000000 : ℝ)|^8335 ≤ (2729937226277/6250000000000 : ℝ)^6287
        have hw : |(2676896409/5000000000 : ℝ)|=(2676896409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45276637/200000000 : ℝ)|^8335 ≤ (697675796001/5000000000000 : ℝ)^6287
        have hw : |(-45276637/200000000 : ℝ)|=(45276637/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163502671/312500000 : ℝ)|^8335 ≤ (42367488443997/100000000000000 : ℝ)^6287
        have hw : |(163502671/312500000 : ℝ)|=(163502671/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s3_2 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53537929/100000000 : ℝ)*x 0 + (5232085551/10000000000 : ℝ)*x 1 + (-1131915819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53537929/100000000 : ℝ)^8335 ≤ (21839498253679/50000000000000 : ℝ)^6287 := by
    have hnat : (53537929 : ℕ)^8335*50000000000000^6287 ≤ 21839498253679^6287*100000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53537929 100000000 21839498253679 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232085551/10000000000 : ℝ)^8335 ≤ (42367489292097/100000000000000 : ℝ)^6287 := by
    have hnat : (5232085551 : ℕ)^8335*100000000000000^6287 ≤ 42367489292097^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232085551 10000000000 42367489292097 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131915819/5000000000 : ℝ)^8335 ≤ (13953514187663/100000000000000 : ℝ)^6287 := by
    have hnat : (1131915819 : ℕ)^8335*100000000000000^6287 ≤ 13953514187663^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131915819 5000000000 13953514187663 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53537929/100000000 : ℝ), (5232085551/10000000000 : ℝ), (-1131915819/5000000000 : ℝ)] ![(21839498253679/50000000000000 : ℝ), (42367489292097/100000000000000 : ℝ), (13953514187663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53537929/100000000 : ℝ)|^8335 ≤ (21839498253679/50000000000000 : ℝ)^6287
        have hw : |(53537929/100000000 : ℝ)|=(53537929/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232085551/10000000000 : ℝ)|^8335 ≤ (42367489292097/100000000000000 : ℝ)^6287
        have hw : |(5232085551/10000000000 : ℝ)|=(5232085551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1131915819/5000000000 : ℝ)|^8335 ≤ (13953514187663/100000000000000 : ℝ)^6287
        have hw : |(-1131915819/5000000000 : ℝ)|=(1131915819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s3_3 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872483151/2000000000 : ℝ)*x 0 + (2085370719/5000000000 : ℝ)*x 1 + (1140711387/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872483151/2000000000 : ℝ)^8335 ≤ (16647061590469/50000000000000 : ℝ)^6287 := by
    have hnat : (872483151 : ℕ)^8335*50000000000000^6287 ≤ 16647061590469^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872483151 2000000000 16647061590469 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085370719/5000000000 : ℝ)^8335 ≤ (3921093177677/12500000000000 : ℝ)^6287 := by
    have hnat : (2085370719 : ℕ)^8335*12500000000000^6287 ≤ 3921093177677^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085370719 5000000000 3921093177677 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140711387/2500000000 : ℝ)^8335 ≤ (17668565691487/50000000000000 : ℝ)^6287 := by
    have hnat : (1140711387 : ℕ)^8335*50000000000000^6287 ≤ 17668565691487^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140711387 2500000000 17668565691487 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872483151/2000000000 : ℝ), (2085370719/5000000000 : ℝ), (1140711387/2500000000 : ℝ)] ![(16647061590469/50000000000000 : ℝ), (3921093177677/12500000000000 : ℝ), (17668565691487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872483151/2000000000 : ℝ)|^8335 ≤ (16647061590469/50000000000000 : ℝ)^6287
        have hw : |(872483151/2000000000 : ℝ)|=(872483151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085370719/5000000000 : ℝ)|^8335 ≤ (3921093177677/12500000000000 : ℝ)^6287
        have hw : |(2085370719/5000000000 : ℝ)|=(2085370719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140711387/2500000000 : ℝ)|^8335 ≤ (17668565691487/50000000000000 : ℝ)^6287
        have hw : |(1140711387/2500000000 : ℝ)|=(1140711387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s3_4 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163104561/10000000000 : ℝ)*x 0 + (654106311/1250000000 : ℝ)*x 1 + (84818843/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163104561/10000000000 : ℝ)^8335 ≤ (2627289785819/20000000000000 : ℝ)^6287 := by
    have hnat : (2163104561 : ℕ)^8335*20000000000000^6287 ≤ 2627289785819^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163104561 10000000000 2627289785819 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654106311/1250000000 : ℝ)^8335 ≤ (42375701426433/100000000000000 : ℝ)^6287 := by
    have hnat : (654106311 : ℕ)^8335*100000000000000^6287 ≤ 42375701426433^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654106311 1250000000 42375701426433 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84818843/156250000 : ℝ)^8335 ≤ (5560981203469/12500000000000 : ℝ)^6287 := by
    have hnat : (84818843 : ℕ)^8335*12500000000000^6287 ≤ 5560981203469^6287*156250000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84818843 156250000 5560981203469 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163104561/10000000000 : ℝ), (654106311/1250000000 : ℝ), (84818843/156250000 : ℝ)] ![(2627289785819/20000000000000 : ℝ), (42375701426433/100000000000000 : ℝ), (5560981203469/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163104561/10000000000 : ℝ)|^8335 ≤ (2627289785819/20000000000000 : ℝ)^6287
        have hw : |(-2163104561/10000000000 : ℝ)|=(2163104561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654106311/1250000000 : ℝ)|^8335 ≤ (42375701426433/100000000000000 : ℝ)^6287
        have hw : |(654106311/1250000000 : ℝ)|=(654106311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84818843/156250000 : ℝ)|^8335 ≤ (5560981203469/12500000000000 : ℝ)^6287
        have hw : |(84818843/156250000 : ℝ)|=(84818843/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s3_5 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303861111/10000000000 : ℝ)*x 0 + (-2067511283/10000000000 : ℝ)*x 1 + (5428406083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303861111/10000000000 : ℝ)^8335 ≤ (43139748252541/100000000000000 : ℝ)^6287 := by
    have hnat : (5303861111 : ℕ)^8335*100000000000000^6287 ≤ 43139748252541^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303861111 10000000000 43139748252541 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067511283/10000000000 : ℝ)^8335 ≤ (618620034169/5000000000000 : ℝ)^6287 := by
    have hnat : (2067511283 : ℕ)^8335*5000000000000^6287 ≤ 618620034169^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067511283 10000000000 618620034169 5000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428406083/10000000000 : ℝ)^8335 ≤ (695122672673/1562500000000 : ℝ)^6287 := by
    have hnat : (5428406083 : ℕ)^8335*1562500000000^6287 ≤ 695122672673^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428406083 10000000000 695122672673 1562500000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303861111/10000000000 : ℝ), (-2067511283/10000000000 : ℝ), (5428406083/10000000000 : ℝ)] ![(43139748252541/100000000000000 : ℝ), (618620034169/5000000000000 : ℝ), (695122672673/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303861111/10000000000 : ℝ)|^8335 ≤ (43139748252541/100000000000000 : ℝ)^6287
        have hw : |(5303861111/10000000000 : ℝ)|=(5303861111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2067511283/10000000000 : ℝ)|^8335 ≤ (618620034169/5000000000000 : ℝ)^6287
        have hw : |(-2067511283/10000000000 : ℝ)|=(2067511283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428406083/10000000000 : ℝ)|^8335 ≤ (695122672673/1562500000000 : ℝ)^6287
        have hw : |(5428406083/10000000000 : ℝ)|=(5428406083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s3_6 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325965249/2500000000 : ℝ)*x 0 + (5428406267/10000000000 : ℝ)*x 1 + (-2067511187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325965249/2500000000 : ℝ)^8335 ≤ (43139747012473/100000000000000 : ℝ)^6287 := by
    have hnat : (1325965249 : ℕ)^8335*100000000000000^6287 ≤ 43139747012473^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325965249 2500000000 43139747012473 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428406267/10000000000 : ℝ)^8335 ≤ (44487853050239/100000000000000 : ℝ)^6287 := by
    have hnat : (5428406267 : ℕ)^8335*100000000000000^6287 ≤ 44487853050239^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428406267 10000000000 44487853050239 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067511187/10000000000 : ℝ)^8335 ≤ (6186199960879/50000000000000 : ℝ)^6287 := by
    have hnat : (2067511187 : ℕ)^8335*50000000000000^6287 ≤ 6186199960879^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067511187 10000000000 6186199960879 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325965249/2500000000 : ℝ), (5428406267/10000000000 : ℝ), (-2067511187/10000000000 : ℝ)] ![(43139747012473/100000000000000 : ℝ), (44487853050239/100000000000000 : ℝ), (6186199960879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325965249/2500000000 : ℝ)|^8335 ≤ (43139747012473/100000000000000 : ℝ)^6287
        have hw : |(1325965249/2500000000 : ℝ)|=(1325965249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428406267/10000000000 : ℝ)|^8335 ≤ (44487853050239/100000000000000 : ℝ)^6287
        have hw : |(5428406267/10000000000 : ℝ)|=(5428406267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2067511187/10000000000 : ℝ)|^8335 ≤ (6186199960879/50000000000000 : ℝ)^6287
        have hw : |(-2067511187/10000000000 : ℝ)|=(2067511187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s3_7 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362451721/10000000000 : ℝ)*x 0 + (285082761/625000000 : ℝ)*x 1 + (166890853/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362451721/10000000000 : ℝ)^8335 ≤ (8323621773029/25000000000000 : ℝ)^6287 := by
    have hnat : (4362451721 : ℕ)^8335*25000000000000^6287 ≤ 8323621773029^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362451721 10000000000 8323621773029 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285082761/625000000 : ℝ)^8335 ≤ (8830377949427/25000000000000 : ℝ)^6287 := by
    have hnat : (285082761 : ℕ)^8335*25000000000000^6287 ≤ 8830377949427^6287*625000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285082761 625000000 8830377949427 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166890853/400000000 : ℝ)^8335 ≤ (31384001092789/100000000000000 : ℝ)^6287 := by
    have hnat : (166890853 : ℕ)^8335*100000000000000^6287 ≤ 31384001092789^6287*400000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166890853 400000000 31384001092789 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362451721/10000000000 : ℝ), (285082761/625000000 : ℝ), (166890853/400000000 : ℝ)] ![(8323621773029/25000000000000 : ℝ), (8830377949427/25000000000000 : ℝ), (31384001092789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362451721/10000000000 : ℝ)|^8335 ≤ (8323621773029/25000000000000 : ℝ)^6287
        have hw : |(4362451721/10000000000 : ℝ)|=(4362451721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285082761/625000000 : ℝ)|^8335 ≤ (8830377949427/25000000000000 : ℝ)^6287
        have hw : |(285082761/625000000 : ℝ)|=(285082761/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166890853/400000000 : ℝ)|^8335 ≤ (31384001092789/100000000000000 : ℝ)^6287
        have hw : |(166890853/400000000 : ℝ)|=(166890853/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1142_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (907/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2127/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7403/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8251/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (907/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8251/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (907/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8251/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (907/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8251/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (907/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8251/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (907/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8251/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (907/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (907/10000 : ℝ) ^ (4167/1024 : ℝ) ≤ (2864995054159377/50000000000000000000 : ℝ) := by
    have hpowers : (907/10000 : ℝ)^4167 ≤ (2864995054159377/50000000000000000000 : ℝ)^1024 := by
      have hnat : (907 : ℕ)^4167*50000000000000000000^1024 ≤ 2864995054159377^1024*10000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        907 10000 2864995054159377 50000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (907/10000 : ℝ)) (X := (2864995054159377/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8251/50000 : ℝ) ^ (4167/1024 : ℝ) ≤ (13089513103012737/20000000000000000000 : ℝ) := by
    have hpowers : (8251/50000 : ℝ)^4167 ≤ (13089513103012737/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8251 : ℕ)^4167*20000000000000000000^1024 ≤ 13089513103012737^1024*50000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8251 50000 13089513103012737 20000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8251/50000 : ℝ)) (X := (13089513103012737/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002864995054159377/25000000000000000000 : ℝ) ≤ (5000140802886969/5000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (25002864995054159377/25000000000000000000 : ℝ)^1024 ≤ (5000140802886969/5000000000000000 : ℝ)^4167 := by
      have hnat : (25002864995054159377 : ℕ)^1024*5000000000000000^4167 ≤ 5000140802886969^4167*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002864995054159377 25000000000000000000 5000140802886969 5000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000140802886969/5000000000000000 : ℝ)) (X := (25002864995054159377/25000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100071177555623382439/100000000000000000000 : ℝ) ≤ (5000874325176709/5000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (100071177555623382439/100000000000000000000 : ℝ)^1024 ≤ (5000874325176709/5000000000000000 : ℝ)^4167 := by
      have hnat : (100071177555623382439 : ℕ)^1024*5000000000000000^4167 ≤ 5000874325176709^4167*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100071177555623382439 100000000000000000000 5000874325176709 5000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000874325176709/5000000000000000 : ℝ)) (X := (100071177555623382439/100000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10013089513103012737/10000000000000000000 : ℝ) ≤ (5001607847466449/5000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (10013089513103012737/10000000000000000000 : ℝ)^1024 ≤ (5001607847466449/5000000000000000 : ℝ)^4167 := by
      have hnat : (10013089513103012737 : ℕ)^1024*5000000000000000^4167 ≤ 5001607847466449^4167*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10013089513103012737 10000000000000000000 5001607847466449 5000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001607847466449/5000000000000000 : ℝ)) (X := (10013089513103012737/10000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2864995054159377/50000000000000000000 : ℝ) ≤ ((4643467544090008751/4645000000000000000 : ℝ)+2*(36676114487/18580000000000 : ℝ)*(907/10000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (4643467544090008751/4645000000000000000 : ℝ)+2*(36676114487/18580000000000 : ℝ)*(907/10000 : ℝ)=(5000140802886969/5000000000000000 : ℝ) by norm_num, show 1+2*(2864995054159377/50000000000000000000 : ℝ)=(25002864995054159377/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13089513103012737/20000000000000000000 : ℝ)+(2864995054159377/50000000000000000000 : ℝ) ≤ ((4643467544090008751/4645000000000000000 : ℝ)+(36676114487/18580000000000 : ℝ)*((8251/50000 : ℝ)+(907/10000 : ℝ)))^(4167/1024 : ℝ) := by
    rw [show (4643467544090008751/4645000000000000000 : ℝ)+(36676114487/18580000000000 : ℝ)*((8251/50000 : ℝ)+(907/10000 : ℝ))=(5000874325176709/5000000000000000 : ℝ) by norm_num, show 1+(13089513103012737/20000000000000000000 : ℝ)+(2864995054159377/50000000000000000000 : ℝ)=(100071177555623382439/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13089513103012737/20000000000000000000 : ℝ) ≤ ((4643467544090008751/4645000000000000000 : ℝ)+2*(36676114487/18580000000000 : ℝ)*(8251/50000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (4643467544090008751/4645000000000000000 : ℝ)+2*(36676114487/18580000000000 : ℝ)*(8251/50000 : ℝ)=(5001607847466449/5000000000000000 : ℝ) by norm_num, show 1+2*(13089513103012737/20000000000000000000 : ℝ)=(10013089513103012737/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4643467544090008751/4645000000000000000 : ℝ)*(X 1 0+X 2 0)+(36676114487/18580000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (907/10000 : ℝ)) (hi := (8251/50000 : ℝ)) (c := (4643467544090008751/4645000000000000000 : ℝ)) (alpha := (36676114487/18580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4643467544090008751/4645000000000000000 : ℝ)*(X 0 1+X 2 1)+(36676114487/18580000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (907/10000 : ℝ)) (hi := (8251/50000 : ℝ)) (c := (4643467544090008751/4645000000000000000 : ℝ)) (alpha := (36676114487/18580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4643467544090008751/4645000000000000000 : ℝ)*(X 0 2+X 1 2)+(36676114487/18580000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (907/10000 : ℝ)) (hi := (8251/50000 : ℝ)) (c := (4643467544090008751/4645000000000000000 : ℝ)) (alpha := (36676114487/18580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-540771621/2500000000 : ℝ)*X 0 0+(135729377/250000000 : ℝ)*X 0 1+(5232085633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676896409/5000000000 : ℝ)*X 1 0+(-45276637/200000000 : ℝ)*X 1 1+(163502671/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53537929/100000000 : ℝ)*X 2 0+(5232085551/10000000000 : ℝ)*X 2 1+(-1131915819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872483151/2000000000 : ℝ)*X 0 0+(2085370719/5000000000 : ℝ)*X 0 1+(1140711387/2500000000 : ℝ)*X 0 2+(872483151/2000000000 : ℝ)*X 1 0+(2085370719/5000000000 : ℝ)*X 1 1+(1140711387/2500000000 : ℝ)*X 1 2+(872483151/2000000000 : ℝ)*X 2 0+(2085370719/5000000000 : ℝ)*X 2 1+(1140711387/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2163104561/10000000000 : ℝ)*X 0 0+(654106311/1250000000 : ℝ)*X 0 1+(84818843/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303861111/10000000000 : ℝ)*X 1 0+(-2067511283/10000000000 : ℝ)*X 1 1+(5428406083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325965249/2500000000 : ℝ)*X 2 0+(5428406267/10000000000 : ℝ)*X 2 1+(-2067511187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362451721/10000000000 : ℝ)*X 0 0+(285082761/625000000 : ℝ)*X 0 1+(166890853/400000000 : ℝ)*X 0 2+(4362451721/10000000000 : ℝ)*X 1 0+(285082761/625000000 : ℝ)*X 1 1+(166890853/400000000 : ℝ)*X 1 2+(4362451721/10000000000 : ℝ)*X 2 0+(285082761/625000000 : ℝ)*X 2 1+(166890853/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (316147281674799298668672303/58062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (290967499/20000000000000 : ℝ)*(base19) + (34511557/2500000000000 : ℝ)*(base23) + (81424817/100000000000000 : ℝ)*(lower2) + (16603063/25000000000000 : ℝ)*(upper3) + (37890599/20000000000000 : ℝ)*(upper5) + (953031780277851/25000000000000 : ℝ)*(major0) + (953031780277851/25000000000000 : ℝ)*(major1) + (953031780277851/25000000000000 : ℝ)*(major2) + (2536929970895009/50000000000000 : ℝ)*(sp0) + (634235784479451/12500000000000 : ℝ)*(sp1) + (5073886350210823/100000000000000 : ℝ)*(sp2) + (1275177534337703/50000000000000 : ℝ)*(sp3) + (5557776617/20000000000000 : ℝ)*(sp4) + (5630688017/50000000000000 : ℝ)*(sp7) + (2550366330051439/100000000000000 : ℝ)*(f.failure) + (5073887730673103/100000000000000 : ℝ)*(f.sum) + (1197003604663/185800000000000000000000000 : ℝ)*base66 + (156416091407224101/116125000000000000000000000000000 : ℝ)*base67 + (1296462351027775899/116125000000000000000000000000000 : ℝ)*base70 + (265689069770775899/116125000000000000000000000000000 : ℝ)*base72 + (5421967943/1161250000000000000000000 : ℝ)*base74 + (338472170027525899/116125000000000000000000000000000 : ℝ)*base76 + (570109985736275899/116125000000000000000000000000000 : ℝ)*base78 + (831500469815099101/116125000000000000000000000000000 : ℝ)*base79 + (1645240748077/232250000000000000000000000 : ℝ)*base82 + (4516453/2500000000000000000000 : ℝ)*base89 + (4516453/2500000000000000000000 : ℝ)*base91 + (4516453/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1228616907844220769235074507/116125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2004905321/100000000000000 : ℝ)*(base19) + (109693651/5000000000000 : ℝ)*(base23) + (33184269/12500000000000 : ℝ)*(upper3) + (59688289/50000000000000 : ℝ)*(lower4) + (8031171/4000000000000 : ℝ)*(upper5) + (3841989669066919/100000000000000 : ℝ)*(major0) + (3841989669066919/100000000000000 : ℝ)*(major1) + (3841989669066919/100000000000000 : ℝ)*(major2) + (1828834347/5000000000000 : ℝ)*(sp1) + (44518565627/100000000000000 : ℝ)*(sp2) + (2556817096704877/50000000000000 : ℝ)*(sp4) + (2556797805908747/50000000000000 : ℝ)*(sp5) + (1278396870242777/25000000000000 : ℝ)*(sp6) + (102813791682131/4000000000000 : ℝ)*(sp7) + (102813791682131/4000000000000 : ℝ)*(f.failure) + (2556817096704877/50000000000000 : ℝ)*(f.sum) + (458894825313/116125000000000000000000000 : ℝ)*base65 + (1946193793901141831/464500000000000000000000000000000 : ℝ)*base68 + (992066529099358169/464500000000000000000000000000000 : ℝ)*base69 + (3246781102367641831/464500000000000000000000000000000 : ℝ)*base72 + (1044913907989/929000000000000000000000000 : ℝ)*base74 + (1791726504373641831/464500000000000000000000000000000 : ℝ)*base76 + (3190241750820641831/464500000000000000000000000000000 : ℝ)*base78 + (5003639332085641831/464500000000000000000000000000000 : ℝ)*base80 + (80083709349/58062500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (477937/100000000000000000000 : ℝ)*base89 + (477937/100000000000000000000 : ℝ)*base91 + (477937/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1142_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (907/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2127/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7403/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1142_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1142_s4_0 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083042083/5000000000 : ℝ)*x 0 + (337618461/625000000 : ℝ)*x 1 + (657175587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083042083/5000000000 : ℝ)^8335 ≤ (822527738483/6250000000000 : ℝ)^6287 := by
    have hnat : (1083042083 : ℕ)^8335*6250000000000^6287 ≤ 822527738483^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083042083 5000000000 822527738483 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337618461/625000000 : ℝ)^8335 ≤ (70720064937/160000000000 : ℝ)^6287 := by
    have hnat : (337618461 : ℕ)^8335*160000000000^6287 ≤ 70720064937^6287*625000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337618461 625000000 70720064937 160000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657175587/1250000000 : ℝ)^8335 ≤ (10659878894479/25000000000000 : ℝ)^6287 := by
    have hnat : (657175587 : ℕ)^8335*25000000000000^6287 ≤ 10659878894479^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657175587 1250000000 10659878894479 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083042083/5000000000 : ℝ), (337618461/625000000 : ℝ), (657175587/1250000000 : ℝ)] ![(822527738483/6250000000000 : ℝ), (70720064937/160000000000 : ℝ), (10659878894479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083042083/5000000000 : ℝ)|^8335 ≤ (822527738483/6250000000000 : ℝ)^6287
        have hw : |(-1083042083/5000000000 : ℝ)|=(1083042083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337618461/625000000 : ℝ)|^8335 ≤ (70720064937/160000000000 : ℝ)^6287
        have hw : |(337618461/625000000 : ℝ)|=(337618461/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657175587/1250000000 : ℝ)|^8335 ≤ (10659878894479/25000000000000 : ℝ)^6287
        have hw : |(657175587/1250000000 : ℝ)|=(657175587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s4_1 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346980813/10000000000 : ℝ)*x 0 + (-447902689/2000000000 : ℝ)*x 1 + (525740531/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346980813/10000000000 : ℝ)^8335 ≤ (21802665568563/50000000000000 : ℝ)^6287 := by
    have hnat : (5346980813 : ℕ)^8335*50000000000000^6287 ≤ 21802665568563^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346980813 10000000000 21802665568563 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447902689/2000000000 : ℝ)^8335 ≤ (13755146671123/100000000000000 : ℝ)^6287 := by
    have hnat : (447902689 : ℕ)^8335*100000000000000^6287 ≤ 13755146671123^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447902689 2000000000 13755146671123 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525740531/1000000000 : ℝ)^8335 ≤ (42639522179853/100000000000000 : ℝ)^6287 := by
    have hnat : (525740531 : ℕ)^8335*100000000000000^6287 ≤ 42639522179853^6287*1000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525740531 1000000000 42639522179853 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346980813/10000000000 : ℝ), (-447902689/2000000000 : ℝ), (525740531/1000000000 : ℝ)] ![(21802665568563/50000000000000 : ℝ), (13755146671123/100000000000000 : ℝ), (42639522179853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346980813/10000000000 : ℝ)|^8335 ≤ (21802665568563/50000000000000 : ℝ)^6287
        have hw : |(5346980813/10000000000 : ℝ)|=(5346980813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447902689/2000000000 : ℝ)|^8335 ≤ (13755146671123/100000000000000 : ℝ)^6287
        have hw : |(-447902689/2000000000 : ℝ)|=(447902689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525740531/1000000000 : ℝ)|^8335 ≤ (42639522179853/100000000000000 : ℝ)^6287
        have hw : |(525740531/1000000000 : ℝ)|=(525740531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s4_2 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167093163/312500000 : ℝ)*x 0 + (5257404403/10000000000 : ℝ)*x 1 + (-2239514107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167093163/312500000 : ℝ)^8335 ≤ (5450666936779/12500000000000 : ℝ)^6287 := by
    have hnat : (167093163 : ℕ)^8335*12500000000000^6287 ≤ 5450666936779^6287*312500000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167093163 312500000 5450666936779 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257404403/10000000000 : ℝ)^8335 ≤ (42639512427481/100000000000000 : ℝ)^6287 := by
    have hnat : (5257404403 : ℕ)^8335*100000000000000^6287 ≤ 42639512427481^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257404403 10000000000 42639512427481 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239514107/10000000000 : ℝ)^8335 ≤ (1719394007707/12500000000000 : ℝ)^6287 := by
    have hnat : (2239514107 : ℕ)^8335*12500000000000^6287 ≤ 1719394007707^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239514107 10000000000 1719394007707 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167093163/312500000 : ℝ), (5257404403/10000000000 : ℝ), (-2239514107/10000000000 : ℝ)] ![(5450666936779/12500000000000 : ℝ), (42639512427481/100000000000000 : ℝ), (1719394007707/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167093163/312500000 : ℝ)|^8335 ≤ (5450666936779/12500000000000 : ℝ)^6287
        have hw : |(167093163/312500000 : ℝ)|=(167093163/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257404403/10000000000 : ℝ)|^8335 ≤ (42639512427481/100000000000000 : ℝ)^6287
        have hw : |(5257404403/10000000000 : ℝ)|=(5257404403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2239514107/10000000000 : ℝ)|^8335 ≤ (1719394007707/12500000000000 : ℝ)^6287
        have hw : |(-2239514107/10000000000 : ℝ)|=(2239514107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s4_3 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182103719/5000000000 : ℝ)*x 0 + (4222829701/10000000000 : ℝ)*x 1 + (902058513/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182103719/5000000000 : ℝ)^8335 ≤ (832806324399/2500000000000 : ℝ)^6287 := by
    have hnat : (2182103719 : ℕ)^8335*2500000000000^6287 ≤ 832806324399^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182103719 5000000000 832806324399 2500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222829701/10000000000 : ℝ)^8335 ≤ (31889179782929/100000000000000 : ℝ)^6287 := by
    have hnat : (4222829701 : ℕ)^8335*100000000000000^6287 ≤ 31889179782929^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222829701 10000000000 31889179782929 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902058513/2000000000 : ℝ)^8335 ≤ (3479856723137/10000000000000 : ℝ)^6287 := by
    have hnat : (902058513 : ℕ)^8335*10000000000000^6287 ≤ 3479856723137^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902058513 2000000000 3479856723137 10000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182103719/5000000000 : ℝ), (4222829701/10000000000 : ℝ), (902058513/2000000000 : ℝ)] ![(832806324399/2500000000000 : ℝ), (31889179782929/100000000000000 : ℝ), (3479856723137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182103719/5000000000 : ℝ)|^8335 ≤ (832806324399/2500000000000 : ℝ)^6287
        have hw : |(2182103719/5000000000 : ℝ)|=(2182103719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222829701/10000000000 : ℝ)|^8335 ≤ (31889179782929/100000000000000 : ℝ)^6287
        have hw : |(4222829701/10000000000 : ℝ)|=(4222829701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902058513/2000000000 : ℝ)|^8335 ≤ (3479856723137/10000000000000 : ℝ)^6287
        have hw : |(902058513/2000000000 : ℝ)|=(902058513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s4_4 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166091357/10000000000 : ℝ)*x 0 + (105156327/200000000 : ℝ)*x 1 + (675185249/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166091357/10000000000 : ℝ)^8335 ≤ (3290125434543/25000000000000 : ℝ)^6287 := by
    have hnat : (2166091357 : ℕ)^8335*25000000000000^6287 ≤ 3290125434543^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166091357 10000000000 3290125434543 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105156327/200000000 : ℝ)^8335 ≤ (2132197093911/5000000000000 : ℝ)^6287 := by
    have hnat : (105156327 : ℕ)^8335*5000000000000^6287 ≤ 2132197093911^6287*200000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105156327 200000000 2132197093911 5000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675185249/1250000000 : ℝ)^8335 ≤ (44195556365809/100000000000000 : ℝ)^6287 := by
    have hnat : (675185249 : ℕ)^8335*100000000000000^6287 ≤ 44195556365809^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675185249 1250000000 44195556365809 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166091357/10000000000 : ℝ), (105156327/200000000 : ℝ), (675185249/1250000000 : ℝ)] ![(3290125434543/25000000000000 : ℝ), (2132197093911/5000000000000 : ℝ), (44195556365809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166091357/10000000000 : ℝ)|^8335 ≤ (3290125434543/25000000000000 : ℝ)^6287
        have hw : |(-2166091357/10000000000 : ℝ)|=(2166091357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105156327/200000000 : ℝ)|^8335 ≤ (2132197093911/5000000000000 : ℝ)^6287
        have hw : |(105156327/200000000 : ℝ)|=(105156327/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675185249/1250000000 : ℝ)|^8335 ≤ (44195556365809/100000000000000 : ℝ)^6287
        have hw : |(675185249/1250000000 : ℝ)|=(675185249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s4_5 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655188127/5000000000 : ℝ)*x 0 + (-419087199/2000000000 : ℝ)*x 1 + (1350370457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655188127/5000000000 : ℝ)^8335 ≤ (2160500819301/5000000000000 : ℝ)^6287 := by
    have hnat : (2655188127 : ℕ)^8335*5000000000000^6287 ≤ 2160500819301^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655188127 5000000000 2160500819301 5000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419087199/2000000000 : ℝ)^8335 ≤ (12594429017133/100000000000000 : ℝ)^6287 := by
    have hnat : (419087199 : ℕ)^8335*100000000000000^6287 ≤ 12594429017133^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419087199 2000000000 12594429017133 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350370457/2500000000 : ℝ)^8335 ≤ (44195554586827/100000000000000 : ℝ)^6287 := by
    have hnat : (1350370457 : ℕ)^8335*100000000000000^6287 ≤ 44195554586827^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350370457 2500000000 44195554586827 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655188127/5000000000 : ℝ), (-419087199/2000000000 : ℝ), (1350370457/2500000000 : ℝ)] ![(2160500819301/5000000000000 : ℝ), (12594429017133/100000000000000 : ℝ), (44195554586827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655188127/5000000000 : ℝ)|^8335 ≤ (2160500819301/5000000000000 : ℝ)^6287
        have hw : |(2655188127/5000000000 : ℝ)|=(2655188127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-419087199/2000000000 : ℝ)|^8335 ≤ (12594429017133/100000000000000 : ℝ)^6287
        have hw : |(-419087199/2000000000 : ℝ)|=(419087199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350370457/2500000000 : ℝ)|^8335 ≤ (44195554586827/100000000000000 : ℝ)^6287
        have hw : |(1350370457/2500000000 : ℝ)|=(1350370457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s4_6 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310375881/10000000000 : ℝ)*x 0 + (5401482363/10000000000 : ℝ)*x 1 + (-2095435771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310375881/10000000000 : ℝ)^8335 ≤ (21605006181139/50000000000000 : ℝ)^6287 := by
    have hnat : (5310375881 : ℕ)^8335*50000000000000^6287 ≤ 21605006181139^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310375881 10000000000 21605006181139 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401482363/10000000000 : ℝ)^8335 ≤ (8839112078043/20000000000000 : ℝ)^6287 := by
    have hnat : (5401482363 : ℕ)^8335*20000000000000^6287 ≤ 8839112078043^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401482363 10000000000 8839112078043 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2095435771/10000000000 : ℝ)^8335 ≤ (1574303404029/12500000000000 : ℝ)^6287 := by
    have hnat : (2095435771 : ℕ)^8335*12500000000000^6287 ≤ 1574303404029^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095435771 10000000000 1574303404029 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310375881/10000000000 : ℝ), (5401482363/10000000000 : ℝ), (-2095435771/10000000000 : ℝ)] ![(21605006181139/50000000000000 : ℝ), (8839112078043/20000000000000 : ℝ), (1574303404029/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310375881/10000000000 : ℝ)|^8335 ≤ (21605006181139/50000000000000 : ℝ)^6287
        have hw : |(5310375881/10000000000 : ℝ)|=(5310375881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401482363/10000000000 : ℝ)|^8335 ≤ (8839112078043/20000000000000 : ℝ)^6287
        have hw : |(5401482363/10000000000 : ℝ)|=(5401482363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2095435771/10000000000 : ℝ)|^8335 ≤ (1574303404029/12500000000000 : ℝ)^6287
        have hw : |(-2095435771/10000000000 : ℝ)|=(2095435771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s4_7 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182110527/5000000000 : ℝ)*x 0 + (281842087/625000000 : ℝ)*x 1 + (4223652823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182110527/5000000000 : ℝ)^8335 ≤ (6662478152737/20000000000000 : ℝ)^6287 := by
    have hnat : (2182110527 : ℕ)^8335*20000000000000^6287 ≤ 6662478152737^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182110527 5000000000 6662478152737 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281842087/625000000 : ℝ)^8335 ≤ (4348773554523/12500000000000 : ℝ)^6287 := by
    have hnat : (281842087 : ℕ)^8335*12500000000000^6287 ≤ 4348773554523^6287*625000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281842087 625000000 4348773554523 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223652823/10000000000 : ℝ)^8335 ≤ (31897420783077/100000000000000 : ℝ)^6287 := by
    have hnat : (4223652823 : ℕ)^8335*100000000000000^6287 ≤ 31897420783077^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223652823 10000000000 31897420783077 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182110527/5000000000 : ℝ), (281842087/625000000 : ℝ), (4223652823/10000000000 : ℝ)] ![(6662478152737/20000000000000 : ℝ), (4348773554523/12500000000000 : ℝ), (31897420783077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182110527/5000000000 : ℝ)|^8335 ≤ (6662478152737/20000000000000 : ℝ)^6287
        have hw : |(2182110527/5000000000 : ℝ)|=(2182110527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281842087/625000000 : ℝ)|^8335 ≤ (4348773554523/12500000000000 : ℝ)^6287
        have hw : |(281842087/625000000 : ℝ)|=(281842087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223652823/10000000000 : ℝ)|^8335 ≤ (31897420783077/100000000000000 : ℝ)^6287
        have hw : |(4223652823/10000000000 : ℝ)|=(4223652823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1142_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7403/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2127/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (447/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7403/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2127/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7403/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2127/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7403/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2127/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7403/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2127/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7403/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2127/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7403/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2127/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2127/20000 : ℝ) ^ (4167/1024 : ℝ) ≤ (10951356295363837/100000000000000000000 : ℝ) := by
    have hpowers : (2127/20000 : ℝ)^4167 ≤ (10951356295363837/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2127 : ℕ)^4167*100000000000000000000^1024 ≤ 10951356295363837^1024*20000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2127 20000 10951356295363837 100000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2127/20000 : ℝ)) (X := (10951356295363837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7403/50000 : ℝ) ^ (4167/1024 : ℝ) ≤ (42095192853573533/100000000000000000000 : ℝ) := by
    have hpowers : (7403/50000 : ℝ)^4167 ≤ (42095192853573533/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7403 : ℕ)^4167*100000000000000000000^1024 ≤ 42095192853573533^1024*50000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7403 50000 42095192853573533 100000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7403/50000 : ℝ)) (X := (42095192853573533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010951356295363837/50000000000000000000 : ℝ) ≤ (10000538193551929/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50010951356295363837/50000000000000000000 : ℝ)^1024 ≤ (10000538193551929/10000000000000000 : ℝ)^4167 := by
      have hnat : (50010951356295363837 : ℕ)^1024*10000000000000000^4167 ≤ 10000538193551929^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010951356295363837 50000000000000000000 10000538193551929 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538193551929/10000000000000000 : ℝ)) (X := (50010951356295363837/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005304654914893737/10000000000000000000 : ℝ) ≤ (625081456687683/625000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (10005304654914893737/10000000000000000000 : ℝ)^1024 ≤ (625081456687683/625000000000000 : ℝ)^4167 := by
      have hnat : (10005304654914893737 : ℕ)^1024*625000000000000^4167 ≤ 625081456687683^4167*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005304654914893737 10000000000000000000 625081456687683 625000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625081456687683/625000000000000 : ℝ)) (X := (10005304654914893737/10000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042095192853573533/50000000000000000000 : ℝ) ≤ (10002068420453927/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50042095192853573533/50000000000000000000 : ℝ)^1024 ≤ (10002068420453927/10000000000000000 : ℝ)^4167 := by
      have hnat : (50042095192853573533 : ℕ)^1024*10000000000000000^4167 ≤ 10002068420453927^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042095192853573533 50000000000000000000 10002068420453927 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002068420453927/10000000000000000 : ℝ)) (X := (50042095192853573533/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10951356295363837/100000000000000000000 : ℝ) ≤ ((41695970842202347129/41710000000000000000 : ℝ)+2*(765113450999/417100000000000 : ℝ)*(2127/20000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (41695970842202347129/41710000000000000000 : ℝ)+2*(765113450999/417100000000000 : ℝ)*(2127/20000 : ℝ)=(10000538193551929/10000000000000000 : ℝ) by norm_num, show 1+2*(10951356295363837/100000000000000000000 : ℝ)=(50010951356295363837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42095192853573533/100000000000000000000 : ℝ)+(10951356295363837/100000000000000000000 : ℝ) ≤ ((41695970842202347129/41710000000000000000 : ℝ)+(765113450999/417100000000000 : ℝ)*((7403/50000 : ℝ)+(2127/20000 : ℝ)))^(4167/1024 : ℝ) := by
    rw [show (41695970842202347129/41710000000000000000 : ℝ)+(765113450999/417100000000000 : ℝ)*((7403/50000 : ℝ)+(2127/20000 : ℝ))=(625081456687683/625000000000000 : ℝ) by norm_num, show 1+(42095192853573533/100000000000000000000 : ℝ)+(10951356295363837/100000000000000000000 : ℝ)=(10005304654914893737/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42095192853573533/100000000000000000000 : ℝ) ≤ ((41695970842202347129/41710000000000000000 : ℝ)+2*(765113450999/417100000000000 : ℝ)*(7403/50000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (41695970842202347129/41710000000000000000 : ℝ)+2*(765113450999/417100000000000 : ℝ)*(7403/50000 : ℝ)=(10002068420453927/10000000000000000 : ℝ) by norm_num, show 1+2*(42095192853573533/100000000000000000000 : ℝ)=(50042095192853573533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41695970842202347129/41710000000000000000 : ℝ)*(X 1 0+X 2 0)+(765113450999/417100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (2127/20000 : ℝ)) (hi := (7403/50000 : ℝ)) (c := (41695970842202347129/41710000000000000000 : ℝ)) (alpha := (765113450999/417100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41695970842202347129/41710000000000000000 : ℝ)*(X 0 1+X 2 1)+(765113450999/417100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (2127/20000 : ℝ)) (hi := (7403/50000 : ℝ)) (c := (41695970842202347129/41710000000000000000 : ℝ)) (alpha := (765113450999/417100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41695970842202347129/41710000000000000000 : ℝ)*(X 0 2+X 1 2)+(765113450999/417100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (2127/20000 : ℝ)) (hi := (7403/50000 : ℝ)) (c := (41695970842202347129/41710000000000000000 : ℝ)) (alpha := (765113450999/417100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1083042083/5000000000 : ℝ)*X 0 0+(337618461/625000000 : ℝ)*X 0 1+(657175587/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346980813/10000000000 : ℝ)*X 1 0+(-447902689/2000000000 : ℝ)*X 1 1+(525740531/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167093163/312500000 : ℝ)*X 2 0+(5257404403/10000000000 : ℝ)*X 2 1+(-2239514107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182103719/5000000000 : ℝ)*X 0 0+(4222829701/10000000000 : ℝ)*X 0 1+(902058513/2000000000 : ℝ)*X 0 2+(2182103719/5000000000 : ℝ)*X 1 0+(4222829701/10000000000 : ℝ)*X 1 1+(902058513/2000000000 : ℝ)*X 1 2+(2182103719/5000000000 : ℝ)*X 2 0+(4222829701/10000000000 : ℝ)*X 2 1+(902058513/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2166091357/10000000000 : ℝ)*X 0 0+(105156327/200000000 : ℝ)*X 0 1+(675185249/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655188127/5000000000 : ℝ)*X 1 0+(-419087199/2000000000 : ℝ)*X 1 1+(1350370457/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310375881/10000000000 : ℝ)*X 2 0+(5401482363/10000000000 : ℝ)*X 2 1+(-2095435771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182110527/5000000000 : ℝ)*X 0 0+(281842087/625000000 : ℝ)*X 0 1+(4223652823/10000000000 : ℝ)*X 0 2+(2182110527/5000000000 : ℝ)*X 1 0+(281842087/625000000 : ℝ)*X 1 1+(4223652823/10000000000 : ℝ)*X 1 2+(2182110527/5000000000 : ℝ)*X 2 0+(281842087/625000000 : ℝ)*X 2 1+(4223652823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30363268143489462847062927717/2085500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (894165317/100000000000000 : ℝ)*(base23) + (130381029/100000000000000 : ℝ)*(lower2) + (26558861/6250000000000 : ℝ)*(upper3) + (2879867/800000000000 : ℝ)*(lower4) + (8464923/6250000000000 : ℝ)*(upper5) + (5199811420511803/100000000000000 : ℝ)*(major0) + (5199811420511803/100000000000000 : ℝ)*(major1) + (5199811420511803/100000000000000 : ℝ)*(major2) + (1730218958068177/25000000000000 : ℝ)*(sp0) + (1730218958068177/25000000000000 : ℝ)*(sp1) + (346043331595339/5000000000000 : ℝ)*(sp2) + (1739362838074247/50000000000000 : ℝ)*(sp3) + (8306200611/100000000000000 : ℝ)*(sp6) + (10423647407/50000000000000 : ℝ)*(sp7) + (869686630860827/25000000000000 : ℝ)*(f.failure) + (1730218958068177/25000000000000 : ℝ)*(f.sum) + (1188238518607197/20855000000000000000000000000 : ℝ)*base65 + (11022707307277363587/4171000000000000000000000000000000 : ℝ)*base67 + (28466929575367363587/4171000000000000000000000000000000 : ℝ)*base69 + (101131505004795363587/4171000000000000000000000000000000 : ℝ)*base71 + (64752984175887/20855000000000000000000000000 : ℝ)*base73 + (24231518023615363587/4171000000000000000000000000000000 : ℝ)*base75 + (57480504432238363587/4171000000000000000000000000000000 : ℝ)*base77 + (67757992682102363587/4171000000000000000000000000000000 : ℝ)*base79 + (8906281453299/2606875000000000000000000000 : ℝ)*base81 + (7840871/625000000000000000000 : ℝ)*base90 + (7840871/625000000000000000000 : ℝ)*base92 + (7840871/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (299923546594959965670417759/41710000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468385603/100000000000000 : ℝ)*(base19) + (24701013/5000000000000 : ℝ)*(base23) + (40692409/50000000000000 : ℝ)*(upper3) + (98907609/50000000000000 : ℝ)*(lower4) + (104593059173281/2000000000000 : ℝ)*(major0) + (104593059173281/2000000000000 : ℝ)*(major1) + (104593059173281/2000000000000 : ℝ)*(major2) + (275539719/20000000000000 : ℝ)*(sp1) + (21983385291/100000000000000 : ℝ)*(sp2) + (7135667593/100000000000000 : ℝ)*(sp3) + (6960594748045439/100000000000000 : ℝ)*(sp4) + (174014822549031/2500000000000 : ℝ)*(sp5) + (435035766914993/6250000000000 : ℝ)*(sp6) + (3498703793925489/100000000000000 : ℝ)*(sp7) + (1749355464796541/50000000000000 : ℝ)*(f.failure) + (6960594748045439/100000000000000 : ℝ)*(f.sum) + (14785521463117/4171000000000000000000000000 : ℝ)*base66 + (1220773009389740249/83420000000000000000000000000000 : ℝ)*base67 + (975594125844160249/83420000000000000000000000000000 : ℝ)*base69 + (961532111960060249/83420000000000000000000000000000 : ℝ)*base71 + (2348761102841/1042750000000000000000000000 : ℝ)*base73 + (3778785442531720249/83420000000000000000000000000000 : ℝ)*base75 + (1941468312727680249/83420000000000000000000000000000 : ℝ)*base77 + (1238457718462600249/83420000000000000000000000000000 : ℝ)*base79 + (1832006678707/4171000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (12788993/1250000000000000000000 : ℝ)*base90 + (12788993/1250000000000000000000 : ℝ)*base92 + (12788993/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1142_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7403/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2127/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1142_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1142_s5_0 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-433344909/2000000000 : ℝ)*x 0 + (337182167/625000000 : ℝ)*x 1 + (1315991191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433344909/2000000000 : ℝ)^8335 ≤ (6582801109811/50000000000000 : ℝ)^6287 := by
    have hnat : (433344909 : ℕ)^8335*50000000000000^6287 ≤ 6582801109811^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433344909 2000000000 6582801109811 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337182167/625000000 : ℝ)^8335 ≤ (44124331775547/100000000000000 : ℝ)^6287 := by
    have hnat : (337182167 : ℕ)^8335*100000000000000^6287 ≤ 44124331775547^6287*625000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337182167 625000000 44124331775547 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315991191/2500000000 : ℝ)^8335 ≤ (5338758249007/12500000000000 : ℝ)^6287 := by
    have hnat : (1315991191 : ℕ)^8335*12500000000000^6287 ≤ 5338758249007^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315991191 2500000000 5338758249007 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-433344909/2000000000 : ℝ), (337182167/625000000 : ℝ), (1315991191/2500000000 : ℝ)] ![(6582801109811/50000000000000 : ℝ), (44124331775547/100000000000000 : ℝ), (5338758249007/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-433344909/2000000000 : ℝ)|^8335 ≤ (6582801109811/50000000000000 : ℝ)^6287
        have hw : |(-433344909/2000000000 : ℝ)|=(433344909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337182167/625000000 : ℝ)|^8335 ≤ (44124331775547/100000000000000 : ℝ)^6287
        have hw : |(337182167/625000000 : ℝ)|=(337182167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315991191/2500000000 : ℝ)|^8335 ≤ (5338758249007/12500000000000 : ℝ)^6287
        have hw : |(1315991191/2500000000 : ℝ)|=(1315991191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s5_1 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167038441/312500000 : ℝ)*x 0 + (-89326859/400000000 : ℝ)*x 1 + (5263964833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167038441/312500000 : ℝ)^8335 ≤ (8717280826187/20000000000000 : ℝ)^6287 := by
    have hnat : (167038441 : ℕ)^8335*20000000000000^6287 ≤ 8717280826187^6287*312500000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167038441 312500000 8717280826187 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89326859/400000000 : ℝ)^8335 ≤ (13703529120693/100000000000000 : ℝ)^6287 := by
    have hnat : (89326859 : ℕ)^8335*100000000000000^6287 ≤ 13703529120693^6287*400000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89326859 400000000 13703529120693 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263964833/10000000000 : ℝ)^8335 ≤ (42710066734269/100000000000000 : ℝ)^6287 := by
    have hnat : (5263964833 : ℕ)^8335*100000000000000^6287 ≤ 42710066734269^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263964833 10000000000 42710066734269 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167038441/312500000 : ℝ), (-89326859/400000000 : ℝ), (5263964833/10000000000 : ℝ)] ![(8717280826187/20000000000000 : ℝ), (13703529120693/100000000000000 : ℝ), (42710066734269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167038441/312500000 : ℝ)|^8335 ≤ (8717280826187/20000000000000 : ℝ)^6287
        have hw : |(167038441/312500000 : ℝ)|=(167038441/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89326859/400000000 : ℝ)|^8335 ≤ (13703529120693/100000000000000 : ℝ)^6287
        have hw : |(-89326859/400000000 : ℝ)|=(89326859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263964833/10000000000 : ℝ)|^8335 ≤ (42710066734269/100000000000000 : ℝ)^6287
        have hw : |(5263964833/10000000000 : ℝ)|=(5263964833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s5_2 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345229919/10000000000 : ℝ)*x 0 + (5263965039/10000000000 : ℝ)*x 1 + (-2233171459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345229919/10000000000 : ℝ)^8335 ≤ (5448300255563/12500000000000 : ℝ)^6287 := by
    have hnat : (5345229919 : ℕ)^8335*12500000000000^6287 ≤ 5448300255563^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345229919 10000000000 5448300255563 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263965039/10000000000 : ℝ)^8335 ≤ (42710068950151/100000000000000 : ℝ)^6287 := by
    have hnat : (5263965039 : ℕ)^8335*100000000000000^6287 ≤ 42710068950151^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263965039 10000000000 42710068950151 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2233171459/10000000000 : ℝ)^8335 ≤ (13703528990529/100000000000000 : ℝ)^6287 := by
    have hnat : (2233171459 : ℕ)^8335*100000000000000^6287 ≤ 13703528990529^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233171459 10000000000 13703528990529 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345229919/10000000000 : ℝ), (5263965039/10000000000 : ℝ), (-2233171459/10000000000 : ℝ)] ![(5448300255563/12500000000000 : ℝ), (42710068950151/100000000000000 : ℝ), (13703528990529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345229919/10000000000 : ℝ)|^8335 ≤ (5448300255563/12500000000000 : ℝ)^6287
        have hw : |(5345229919/10000000000 : ℝ)|=(5345229919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263965039/10000000000 : ℝ)|^8335 ≤ (42710068950151/100000000000000 : ℝ)^6287
        have hw : |(5263965039/10000000000 : ℝ)|=(5263965039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2233171459/10000000000 : ℝ)|^8335 ≤ (13703528990529/100000000000000 : ℝ)^6287
        have hw : |(-2233171459/10000000000 : ℝ)|=(2233171459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s5_3 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364578963/10000000000 : ℝ)*x 0 + (4236252657/10000000000 : ℝ)*x 1 + (899354707/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364578963/10000000000 : ℝ)^8335 ≤ (33316012690129/100000000000000 : ℝ)^6287 := by
    have hnat : (4364578963 : ℕ)^8335*100000000000000^6287 ≤ 33316012690129^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364578963 10000000000 33316012690129 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236252657/10000000000 : ℝ)^8335 ≤ (32023634090199/100000000000000 : ℝ)^6287 := by
    have hnat : (4236252657 : ℕ)^8335*100000000000000^6287 ≤ 32023634090199^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236252657 10000000000 32023634090199 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899354707/2000000000 : ℝ)^8335 ≤ (17330176604269/50000000000000 : ℝ)^6287 := by
    have hnat : (899354707 : ℕ)^8335*50000000000000^6287 ≤ 17330176604269^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899354707 2000000000 17330176604269 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364578963/10000000000 : ℝ), (4236252657/10000000000 : ℝ), (899354707/2000000000 : ℝ)] ![(33316012690129/100000000000000 : ℝ), (32023634090199/100000000000000 : ℝ), (17330176604269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364578963/10000000000 : ℝ)|^8335 ≤ (33316012690129/100000000000000 : ℝ)^6287
        have hw : |(4364578963/10000000000 : ℝ)|=(4364578963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236252657/10000000000 : ℝ)|^8335 ≤ (32023634090199/100000000000000 : ℝ)^6287
        have hw : |(4236252657/10000000000 : ℝ)|=(4236252657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899354707/2000000000 : ℝ)|^8335 ≤ (17330176604269/50000000000000 : ℝ)^6287
        have hw : |(899354707/2000000000 : ℝ)|=(899354707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s5_4 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-17333837/80000000 : ℝ)*x 0 + (2632151817/5000000000 : ℝ)*x 1 + (2697287361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17333837/80000000 : ℝ)^8335 ≤ (6582821571103/50000000000000 : ℝ)^6287 := by
    have hnat : (17333837 : ℕ)^8335*50000000000000^6287 ≤ 6582821571103^6287*80000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17333837 80000000 6582821571103 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632151817/5000000000 : ℝ)^8335 ≤ (8542742231239/20000000000000 : ℝ)^6287 := by
    have hnat : (2632151817 : ℕ)^8335*20000000000000^6287 ≤ 8542742231239^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632151817 5000000000 8542742231239 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697287361/5000000000 : ℝ)^8335 ≤ (5515080710313/12500000000000 : ℝ)^6287 := by
    have hnat : (2697287361 : ℕ)^8335*12500000000000^6287 ≤ 5515080710313^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697287361 5000000000 5515080710313 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17333837/80000000 : ℝ), (2632151817/5000000000 : ℝ), (2697287361/5000000000 : ℝ)] ![(6582821571103/50000000000000 : ℝ), (8542742231239/20000000000000 : ℝ), (5515080710313/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17333837/80000000 : ℝ)|^8335 ≤ (6582821571103/50000000000000 : ℝ)^6287
        have hw : |(-17333837/80000000 : ℝ)|=(17333837/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632151817/5000000000 : ℝ)|^8335 ≤ (8542742231239/20000000000000 : ℝ)^6287
        have hw : |(2632151817/5000000000 : ℝ)|=(2632151817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697287361/5000000000 : ℝ)|^8335 ≤ (5515080710313/12500000000000 : ℝ)^6287
        have hw : |(2697287361/5000000000 : ℝ)|=(2697287361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s5_5 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656027131/5000000000 : ℝ)*x 0 + (-1051280487/5000000000 : ℝ)*x 1 + (1348643703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656027131/5000000000 : ℝ)^8335 ≤ (43228118848593/100000000000000 : ℝ)^6287 := by
    have hnat : (2656027131 : ℕ)^8335*100000000000000^6287 ≤ 43228118848593^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656027131 5000000000 43228118848593 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051280487/5000000000 : ℝ)^8335 ≤ (12651234477647/100000000000000 : ℝ)^6287 := by
    have hnat : (1051280487 : ℕ)^8335*100000000000000^6287 ≤ 12651234477647^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051280487 5000000000 12651234477647 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348643703/2500000000 : ℝ)^8335 ≤ (689385104037/1562500000000 : ℝ)^6287 := by
    have hnat : (1348643703 : ℕ)^8335*1562500000000^6287 ≤ 689385104037^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348643703 2500000000 689385104037 1562500000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656027131/5000000000 : ℝ), (-1051280487/5000000000 : ℝ), (1348643703/2500000000 : ℝ)] ![(43228118848593/100000000000000 : ℝ), (12651234477647/100000000000000 : ℝ), (689385104037/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656027131/5000000000 : ℝ)|^8335 ≤ (43228118848593/100000000000000 : ℝ)^6287
        have hw : |(2656027131/5000000000 : ℝ)|=(2656027131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1051280487/5000000000 : ℝ)|^8335 ≤ (12651234477647/100000000000000 : ℝ)^6287
        have hw : |(-1051280487/5000000000 : ℝ)|=(1051280487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348643703/2500000000 : ℝ)|^8335 ≤ (689385104037/1562500000000 : ℝ)^6287
        have hw : |(1348643703/2500000000 : ℝ)|=(1348643703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s5_6 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656026897/5000000000 : ℝ)*x 0 + (5394575109/10000000000 : ℝ)*x 1 + (-2102561203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656026897/5000000000 : ℝ)^8335 ≤ (21614056899759/50000000000000 : ℝ)^6287 := by
    have hnat : (2656026897 : ℕ)^8335*50000000000000^6287 ≤ 21614056899759^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656026897 5000000000 21614056899759 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394575109/10000000000 : ℝ)^8335 ≤ (137877030871/312500000000 : ℝ)^6287 := by
    have hnat : (5394575109 : ℕ)^8335*312500000000^6287 ≤ 137877030871^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394575109 10000000000 137877030871 312500000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2102561203/10000000000 : ℝ)^8335 ≤ (12651236304409/100000000000000 : ℝ)^6287 := by
    have hnat : (2102561203 : ℕ)^8335*100000000000000^6287 ≤ 12651236304409^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102561203 10000000000 12651236304409 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656026897/5000000000 : ℝ), (5394575109/10000000000 : ℝ), (-2102561203/10000000000 : ℝ)] ![(21614056899759/50000000000000 : ℝ), (137877030871/312500000000 : ℝ), (12651236304409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656026897/5000000000 : ℝ)|^8335 ≤ (21614056899759/50000000000000 : ℝ)^6287
        have hw : |(2656026897/5000000000 : ℝ)|=(2656026897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394575109/10000000000 : ℝ)|^8335 ≤ (137877030871/312500000000 : ℝ)^6287
        have hw : |(5394575109/10000000000 : ℝ)|=(5394575109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2102561203/10000000000 : ℝ)|^8335 ≤ (12651236304409/100000000000000 : ℝ)^6287
        have hw : |(-2102561203/10000000000 : ℝ)|=(2102561203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s5_7 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218229489/500000000 : ℝ)*x 0 + (70251563/156250000 : ℝ)*x 1 + (529616053/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218229489/500000000 : ℝ)^8335 ≤ (33316122156271/100000000000000 : ℝ)^6287 := by
    have hnat : (218229489 : ℕ)^8335*100000000000000^6287 ≤ 33316122156271^6287*500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218229489 500000000 33316122156271 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70251563/156250000 : ℝ)^8335 ≤ (17326735537849/50000000000000 : ℝ)^6287 := by
    have hnat : (70251563 : ℕ)^8335*50000000000000^6287 ≤ 17326735537849^6287*156250000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70251563 156250000 17326735537849 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529616053/1250000000 : ℝ)^8335 ≤ (32030406748541/100000000000000 : ℝ)^6287 := by
    have hnat : (529616053 : ℕ)^8335*100000000000000^6287 ≤ 32030406748541^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529616053 1250000000 32030406748541 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218229489/500000000 : ℝ), (70251563/156250000 : ℝ), (529616053/1250000000 : ℝ)] ![(33316122156271/100000000000000 : ℝ), (17326735537849/50000000000000 : ℝ), (32030406748541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218229489/500000000 : ℝ)|^8335 ≤ (33316122156271/100000000000000 : ℝ)^6287
        have hw : |(218229489/500000000 : ℝ)|=(218229489/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70251563/156250000 : ℝ)|^8335 ≤ (17326735537849/50000000000000 : ℝ)^6287
        have hw : |(70251563/156250000 : ℝ)|=(70251563/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529616053/1250000000 : ℝ)|^8335 ≤ (32030406748541/100000000000000 : ℝ)^6287
        have hw : |(529616053/1250000000 : ℝ)|=(529616053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1142_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2263/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14089/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (447/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (447/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (447/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (447/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (447/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (447/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (447/4000 : ℝ) ^ (4167/1024 : ℝ) ≤ (6698375379316217/50000000000000000000 : ℝ) := by
    have hpowers : (447/4000 : ℝ)^4167 ≤ (6698375379316217/50000000000000000000 : ℝ)^1024 := by
      have hnat : (447 : ℕ)^4167*50000000000000000000^1024 ≤ 6698375379316217^1024*4000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        447 4000 6698375379316217 50000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (447/4000 : ℝ)) (X := (6698375379316217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (4167/1024 : ℝ) ≤ (17934824729278913/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^4167 ≤ (17934824729278913/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4167*50000000000000000000^1024 ≤ 17934824729278913^1024*20000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 17934824729278913 50000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (17934824729278913/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006698375379316217/25000000000000000000 : ℝ) ≤ (2000131671579683/2000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (25006698375379316217/25000000000000000000 : ℝ)^1024 ≤ (2000131671579683/2000000000000000 : ℝ)^4167 := by
      have hnat : (25006698375379316217 : ℕ)^1024*2000000000000000^4167 ≤ 2000131671579683^4167*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006698375379316217 25000000000000000000 2000131671579683 2000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000131671579683/2000000000000000 : ℝ)) (X := (25006698375379316217/25000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002463320010859513/5000000000000000000 : ℝ) ≤ (5000605224660693/5000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (5002463320010859513/5000000000000000000 : ℝ)^1024 ≤ (5000605224660693/5000000000000000 : ℝ)^4167 := by
      have hnat : (5002463320010859513 : ℕ)^1024*5000000000000000^4167 ≤ 5000605224660693^4167*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002463320010859513 5000000000000000000 5000605224660693 5000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000605224660693/5000000000000000 : ℝ)) (X := (5002463320010859513/5000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017934824729278913/25000000000000000000 : ℝ) ≤ (10001762540744357/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (25017934824729278913/25000000000000000000 : ℝ)^1024 ≤ (10001762540744357/10000000000000000 : ℝ)^4167 := by
      have hnat : (25017934824729278913 : ℕ)^1024*10000000000000000^4167 ≤ 10001762540744357^4167*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017934824729278913 25000000000000000000 10001762540744357 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001762540744357/10000000000000000 : ℝ)) (X := (25017934824729278913/25000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6698375379316217/50000000000000000000 : ℝ) ≤ ((203931168879104987/204000000000000000 : ℝ)+2*(552091422971/306000000000000 : ℝ)*(447/4000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (203931168879104987/204000000000000000 : ℝ)+2*(552091422971/306000000000000 : ℝ)*(447/4000 : ℝ)=(2000131671579683/2000000000000000 : ℝ) by norm_num, show 1+2*(6698375379316217/50000000000000000000 : ℝ)=(25006698375379316217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17934824729278913/50000000000000000000 : ℝ)+(6698375379316217/50000000000000000000 : ℝ) ≤ ((203931168879104987/204000000000000000 : ℝ)+(552091422971/306000000000000 : ℝ)*((2847/20000 : ℝ)+(447/4000 : ℝ)))^(4167/1024 : ℝ) := by
    rw [show (203931168879104987/204000000000000000 : ℝ)+(552091422971/306000000000000 : ℝ)*((2847/20000 : ℝ)+(447/4000 : ℝ))=(5000605224660693/5000000000000000 : ℝ) by norm_num, show 1+(17934824729278913/50000000000000000000 : ℝ)+(6698375379316217/50000000000000000000 : ℝ)=(5002463320010859513/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17934824729278913/50000000000000000000 : ℝ) ≤ ((203931168879104987/204000000000000000 : ℝ)+2*(552091422971/306000000000000 : ℝ)*(2847/20000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (203931168879104987/204000000000000000 : ℝ)+2*(552091422971/306000000000000 : ℝ)*(2847/20000 : ℝ)=(10001762540744357/10000000000000000 : ℝ) by norm_num, show 1+2*(17934824729278913/50000000000000000000 : ℝ)=(25017934824729278913/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (203931168879104987/204000000000000000 : ℝ)*(X 1 0+X 2 0)+(552091422971/306000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (447/4000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (203931168879104987/204000000000000000 : ℝ)) (alpha := (552091422971/306000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (203931168879104987/204000000000000000 : ℝ)*(X 0 1+X 2 1)+(552091422971/306000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (447/4000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (203931168879104987/204000000000000000 : ℝ)) (alpha := (552091422971/306000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (203931168879104987/204000000000000000 : ℝ)*(X 0 2+X 1 2)+(552091422971/306000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (447/4000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (203931168879104987/204000000000000000 : ℝ)) (alpha := (552091422971/306000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-433344909/2000000000 : ℝ)*X 0 0+(337182167/625000000 : ℝ)*X 0 1+(1315991191/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167038441/312500000 : ℝ)*X 1 0+(-89326859/400000000 : ℝ)*X 1 1+(5263964833/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345229919/10000000000 : ℝ)*X 2 0+(5263965039/10000000000 : ℝ)*X 2 1+(-2233171459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364578963/10000000000 : ℝ)*X 0 0+(4236252657/10000000000 : ℝ)*X 0 1+(899354707/2000000000 : ℝ)*X 0 2+(4364578963/10000000000 : ℝ)*X 1 0+(4236252657/10000000000 : ℝ)*X 1 1+(899354707/2000000000 : ℝ)*X 1 2+(4364578963/10000000000 : ℝ)*X 2 0+(4236252657/10000000000 : ℝ)*X 2 1+(899354707/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-17333837/80000000 : ℝ)*X 0 0+(2632151817/5000000000 : ℝ)*X 0 1+(2697287361/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656027131/5000000000 : ℝ)*X 1 0+(-1051280487/5000000000 : ℝ)*X 1 1+(1348643703/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656026897/5000000000 : ℝ)*X 2 0+(5394575109/10000000000 : ℝ)*X 2 1+(-2102561203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218229489/500000000 : ℝ)*X 0 0+(70251563/156250000 : ℝ)*X 0 1+(529616053/1250000000 : ℝ)*X 0 2+(218229489/500000000 : ℝ)*X 1 0+(70251563/156250000 : ℝ)*X 1 1+(529616053/1250000000 : ℝ)*X 1 2+(218229489/500000000 : ℝ)*X 2 0+(70251563/156250000 : ℝ)*X 2 1+(529616053/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78119314513007117139718159/10200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17915771/1000000000000 : ℝ)*(base19) + (726409049/50000000000000 : ℝ)*(base23) + (239416369/100000000000000 : ℝ)*(upper3) + (16843927/50000000000000 : ℝ)*(upper4) + (167405783/100000000000000 : ℝ)*(upper5) + (5737561709865919/100000000000000 : ℝ)*(major0) + (5737561709865919/100000000000000 : ℝ)*(major1) + (5737561709865919/100000000000000 : ℝ)*(major2) + (7636563512809379/100000000000000 : ℝ)*(sp0) + (7636612389151871/100000000000000 : ℝ)*(sp1) + (954576590988859/12500000000000 : ℝ)*(sp2) + (959621561589259/25000000000000 : ℝ)*(sp3) + (50667919593/100000000000000 : ℝ)*(sp4) + (4547470789/20000000000000 : ℝ)*(sp7) + (3838508983710981/100000000000000 : ℝ)*(f.failure) + (7636614180728971/100000000000000 : ℝ)*(f.sum) + (21990113128949/15300000000000000000000000000 : ℝ)*base65 + (354521850436987841/61200000000000000000000000000000 : ℝ)*base68 + (1077076229356987841/61200000000000000000000000000000 : ℝ)*base70 + (123286453149412159/61200000000000000000000000000000 : ℝ)*base71 + (58256841770249/15300000000000000000000000000 : ℝ)*base73 + (49473323226187841/61200000000000000000000000000000 : ℝ)*base76 + (878523263589787841/61200000000000000000000000000000 : ℝ)*base78 + (847446494853412159/61200000000000000000000000000000 : ℝ)*base79 + (36174634437749/15300000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (7596887/2500000000000000000000 : ℝ)*base89 + (7596887/2500000000000000000000 : ℝ)*base91 + (7596887/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5100039067480884511771/850000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2245752381/100000000000000 : ℝ)*(base19) + (1003690773/50000000000000 : ℝ)*(base23) + (224524847/100000000000000 : ℝ)*(upper3) + (228002709/100000000000000 : ℝ)*(lower4) + (6704001/25000000000000 : ℝ)*(upper5) + (2883680813167699/50000000000000 : ℝ)*(major0) + (2883680813167699/50000000000000 : ℝ)*(major1) + (2883680813167699/50000000000000 : ℝ)*(major2) + (67286291429/100000000000000 : ℝ)*(sp1) + (6867923701/10000000000000 : ℝ)*(sp2) + (3838138754148031/50000000000000 : ℝ)*(sp4) + (1919051994063063/25000000000000 : ℝ)*(sp5) + (1535241364335501/20000000000000 : ℝ)*(sp6) + (1929222772186597/50000000000000 : ℝ)*(sp7) + (1929222772186597/50000000000000 : ℝ)*(f.failure) + (3838138754148031/50000000000000 : ℝ)*(f.sum) + (49359241453229/7650000000000000000000000000 : ℝ)*base65 + (173257097612502739/30600000000000000000000000000000 : ℝ)*base67 + (325516155209897261/30600000000000000000000000000000 : ℝ)*base70 + (150094138993097261/30600000000000000000000000000000 : ℝ)*base72 + (10217095278479/7650000000000000000000000000 : ℝ)*base73 + (387909129349902739/30600000000000000000000000000000 : ℝ)*base75 + (171569160485897261/30600000000000000000000000000000 : ℝ)*base78 + (430339107526302739/30600000000000000000000000000000 : ℝ)*base79 + (28927548158579/7650000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5372919/1250000000000000000000 : ℝ)*base89 + (5372919/1250000000000000000000 : ℝ)*base91 + (5372919/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1142_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1142_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1142_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (907/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1142_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1142_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1142_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (907/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1142_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
