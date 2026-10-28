-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1262_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:54:59.354019+00:00
-- url     : https://prove2.me/submissions/d13c5681-a443-474e-99f2-164eee194c46

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
theorem support_rectangle_w1262_s6_0 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055387189/5000000000 : ℝ)*x 0 + (2695495111/5000000000 : ℝ)*x 1 + (2633659639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055387189/5000000000 : ℝ)^8455 ≤ (6419029706609/50000000000000 : ℝ)^6407 := by
    have hnat : (1055387189 : ℕ)^8455*50000000000000^6407 ≤ 6419029706609^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055387189 5000000000 6419029706609 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695495111/5000000000 : ℝ)^8455 ≤ (44248269606193/100000000000000 : ℝ)^6407 := by
    have hnat : (2695495111 : ℕ)^8455*100000000000000^6407 ≤ 44248269606193^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695495111 5000000000 44248269606193 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633659639/5000000000 : ℝ)^8455 ≤ (10728417743387/25000000000000 : ℝ)^6407 := by
    have hnat : (2633659639 : ℕ)^8455*25000000000000^6407 ≤ 10728417743387^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633659639 5000000000 10728417743387 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055387189/5000000000 : ℝ), (2695495111/5000000000 : ℝ), (2633659639/5000000000 : ℝ)] ![(6419029706609/50000000000000 : ℝ), (44248269606193/100000000000000 : ℝ), (10728417743387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055387189/5000000000 : ℝ)|^8455 ≤ (6419029706609/50000000000000 : ℝ)^6407
        have hw : |(-1055387189/5000000000 : ℝ)|=(1055387189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695495111/5000000000 : ℝ)|^8455 ≤ (44248269606193/100000000000000 : ℝ)^6407
        have hw : |(2695495111/5000000000 : ℝ)|=(2695495111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633659639/5000000000 : ℝ)|^8455 ≤ (10728417743387/25000000000000 : ℝ)^6407
        have hw : |(2633659639/5000000000 : ℝ)|=(2633659639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s6_1 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344242723/10000000000 : ℝ)*x 0 + (-1086738213/5000000000 : ℝ)*x 1 + (5267319273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344242723/10000000000 : ℝ)^8455 ≤ (43742629497237/100000000000000 : ℝ)^6407 := by
    have hnat : (5344242723 : ℕ)^8455*100000000000000^6407 ≤ 43742629497237^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344242723 10000000000 43742629497237 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086738213/5000000000 : ℝ)^8455 ≤ (13343699568231/100000000000000 : ℝ)^6407 := by
    have hnat : (1086738213 : ℕ)^8455*100000000000000^6407 ≤ 13343699568231^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086738213 5000000000 13343699568231 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267319273/10000000000 : ℝ)^8455 ≤ (42913670919791/100000000000000 : ℝ)^6407 := by
    have hnat : (5267319273 : ℕ)^8455*100000000000000^6407 ≤ 42913670919791^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267319273 10000000000 42913670919791 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344242723/10000000000 : ℝ), (-1086738213/5000000000 : ℝ), (5267319273/10000000000 : ℝ)] ![(43742629497237/100000000000000 : ℝ), (13343699568231/100000000000000 : ℝ), (42913670919791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344242723/10000000000 : ℝ)|^8455 ≤ (43742629497237/100000000000000 : ℝ)^6407
        have hw : |(5344242723/10000000000 : ℝ)|=(5344242723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1086738213/5000000000 : ℝ)|^8455 ≤ (13343699568231/100000000000000 : ℝ)^6407
        have hw : |(-1086738213/5000000000 : ℝ)|=(1086738213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267319273/10000000000 : ℝ)|^8455 ≤ (42913670919791/100000000000000 : ℝ)^6407
        have hw : |(5267319273/10000000000 : ℝ)|=(5267319273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s6_2 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668030341/1250000000 : ℝ)*x 0 + (5267319273/10000000000 : ℝ)*x 1 + (-108673821/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668030341/1250000000 : ℝ)^8455 ≤ (43742629551243/100000000000000 : ℝ)^6407 := by
    have hnat : (668030341 : ℕ)^8455*100000000000000^6407 ≤ 43742629551243^6407*1250000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668030341 1250000000 43742629551243 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267319273/10000000000 : ℝ)^8455 ≤ (42913670919791/100000000000000 : ℝ)^6407 := by
    have hnat : (5267319273 : ℕ)^8455*100000000000000^6407 ≤ 42913670919791^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267319273 10000000000 42913670919791 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108673821/500000000 : ℝ)^8455 ≤ (667184975981/5000000000000 : ℝ)^6407 := by
    have hnat : (108673821 : ℕ)^8455*5000000000000^6407 ≤ 667184975981^6407*500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108673821 500000000 667184975981 5000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668030341/1250000000 : ℝ), (5267319273/10000000000 : ℝ), (-108673821/500000000 : ℝ)] ![(43742629551243/100000000000000 : ℝ), (42913670919791/100000000000000 : ℝ), (667184975981/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668030341/1250000000 : ℝ)|^8455 ≤ (43742629551243/100000000000000 : ℝ)^6407
        have hw : |(668030341/1250000000 : ℝ)|=(668030341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267319273/10000000000 : ℝ)|^8455 ≤ (42913670919791/100000000000000 : ℝ)^6407
        have hw : |(5267319273/10000000000 : ℝ)|=(5267319273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108673821/500000000 : ℝ)|^8455 ≤ (667184975981/5000000000000 : ℝ)^6407
        have hw : |(-108673821/500000000 : ℝ)|=(108673821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s6_3 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087007323/2500000000 : ℝ)*x 0 + (1055967939/2500000000 : ℝ)*x 1 + (4475716179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087007323/2500000000 : ℝ)^8455 ≤ (33317507803133/100000000000000 : ℝ)^6407 := by
    have hnat : (1087007323 : ℕ)^8455*100000000000000^6407 ≤ 33317507803133^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087007323 2500000000 33317507803133 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055967939/2500000000 : ℝ)^8455 ≤ (8016947179431/25000000000000 : ℝ)^6407 := by
    have hnat : (1055967939 : ℕ)^8455*25000000000000^6407 ≤ 8016947179431^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055967939 2500000000 8016947179431 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475716179/10000000000 : ℝ)^8455 ≤ (1730735173453/5000000000000 : ℝ)^6407 := by
    have hnat : (4475716179 : ℕ)^8455*5000000000000^6407 ≤ 1730735173453^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475716179 10000000000 1730735173453 5000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087007323/2500000000 : ℝ), (1055967939/2500000000 : ℝ), (4475716179/10000000000 : ℝ)] ![(33317507803133/100000000000000 : ℝ), (8016947179431/25000000000000 : ℝ), (1730735173453/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087007323/2500000000 : ℝ)|^8455 ≤ (33317507803133/100000000000000 : ℝ)^6407
        have hw : |(1087007323/2500000000 : ℝ)|=(1087007323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055967939/2500000000 : ℝ)|^8455 ≤ (8016947179431/25000000000000 : ℝ)^6407
        have hw : |(1055967939/2500000000 : ℝ)|=(1055967939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475716179/10000000000 : ℝ)|^8455 ≤ (1730735173453/5000000000000 : ℝ)^6407
        have hw : |(4475716179/10000000000 : ℝ)|=(4475716179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s6_4 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055389591/5000000000 : ℝ)*x 0 + (1316907929/2500000000 : ℝ)*x 1 + (2695338263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055389591/5000000000 : ℝ)^8455 ≤ (1604762246459/12500000000000 : ℝ)^6407 := by
    have hnat : (1055389591 : ℕ)^8455*12500000000000^6407 ≤ 1604762246459^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055389591 5000000000 1604762246459 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316907929/2500000000 : ℝ)^8455 ≤ (21458515075233/50000000000000 : ℝ)^6407 := by
    have hnat : (1316907929 : ℕ)^8455*50000000000000^6407 ≤ 21458515075233^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316907929 2500000000 21458515075233 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695338263/5000000000 : ℝ)^8455 ≤ (44244871854971/100000000000000 : ℝ)^6407 := by
    have hnat : (2695338263 : ℕ)^8455*100000000000000^6407 ≤ 44244871854971^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695338263 5000000000 44244871854971 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055389591/5000000000 : ℝ), (1316907929/2500000000 : ℝ), (2695338263/5000000000 : ℝ)] ![(1604762246459/12500000000000 : ℝ), (21458515075233/50000000000000 : ℝ), (44244871854971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055389591/5000000000 : ℝ)|^8455 ≤ (1604762246459/12500000000000 : ℝ)^6407
        have hw : |(-1055389591/5000000000 : ℝ)|=(1055389591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316907929/2500000000 : ℝ)|^8455 ≤ (21458515075233/50000000000000 : ℝ)^6407
        have hw : |(1316907929/2500000000 : ℝ)|=(1316907929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695338263/5000000000 : ℝ)|^8455 ≤ (44244871854971/100000000000000 : ℝ)^6407
        have hw : |(2695338263/5000000000 : ℝ)|=(2695338263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s6_5 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312645321/10000000000 : ℝ)*x 0 + (-2050119461/10000000000 : ℝ)*x 1 + (1347669031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312645321/10000000000 : ℝ)^8455 ≤ (43401658185091/100000000000000 : ℝ)^6407 := by
    have hnat : (5312645321 : ℕ)^8455*100000000000000^6407 ≤ 43401658185091^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312645321 10000000000 43401658185091 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050119461/10000000000 : ℝ)^8455 ≤ (12353474303929/100000000000000 : ℝ)^6407 := by
    have hnat : (2050119461 : ℕ)^8455*100000000000000^6407 ≤ 12353474303929^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050119461 10000000000 12353474303929 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347669031/2500000000 : ℝ)^8455 ≤ (5530608437601/12500000000000 : ℝ)^6407 := by
    have hnat : (1347669031 : ℕ)^8455*12500000000000^6407 ≤ 5530608437601^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347669031 2500000000 5530608437601 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312645321/10000000000 : ℝ), (-2050119461/10000000000 : ℝ), (1347669031/2500000000 : ℝ)] ![(43401658185091/100000000000000 : ℝ), (12353474303929/100000000000000 : ℝ), (5530608437601/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312645321/10000000000 : ℝ)|^8455 ≤ (43401658185091/100000000000000 : ℝ)^6407
        have hw : |(5312645321/10000000000 : ℝ)|=(5312645321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050119461/10000000000 : ℝ)|^8455 ≤ (12353474303929/100000000000000 : ℝ)^6407
        have hw : |(-2050119461/10000000000 : ℝ)|=(2050119461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347669031/2500000000 : ℝ)|^8455 ≤ (5530608437601/12500000000000 : ℝ)^6407
        have hw : |(1347669031/2500000000 : ℝ)|=(1347669031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s6_6 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062528951/2000000000 : ℝ)*x 0 + (107813523/200000000 : ℝ)*x 1 + (-2050120193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062528951/2000000000 : ℝ)^8455 ≤ (43401652083111/100000000000000 : ℝ)^6407 := by
    have hnat : (1062528951 : ℕ)^8455*100000000000000^6407 ≤ 43401652083111^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062528951 2000000000 43401652083111 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107813523/200000000 : ℝ)^8455 ≤ (44244867782421/100000000000000 : ℝ)^6407 := by
    have hnat : (107813523 : ℕ)^8455*100000000000000^6407 ≤ 44244867782421^6407*200000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107813523 200000000 44244867782421 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050120193/10000000000 : ℝ)^8455 ≤ (3088370031173/25000000000000 : ℝ)^6407 := by
    have hnat : (2050120193 : ℕ)^8455*25000000000000^6407 ≤ 3088370031173^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050120193 10000000000 3088370031173 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062528951/2000000000 : ℝ), (107813523/200000000 : ℝ), (-2050120193/10000000000 : ℝ)] ![(43401652083111/100000000000000 : ℝ), (44244867782421/100000000000000 : ℝ), (3088370031173/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062528951/2000000000 : ℝ)|^8455 ≤ (43401652083111/100000000000000 : ℝ)^6407
        have hw : |(1062528951/2000000000 : ℝ)|=(1062528951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107813523/200000000 : ℝ)|^8455 ≤ (44244867782421/100000000000000 : ℝ)^6407
        have hw : |(107813523/200000000 : ℝ)|=(107813523/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2050120193/10000000000 : ℝ)|^8455 ≤ (3088370031173/25000000000000 : ℝ)^6407
        have hw : |(-2050120193/10000000000 : ℝ)|=(2050120193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s6_7 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348038561/10000000000 : ℝ)*x 0 + (4475079107/10000000000 : ℝ)*x 1 + (844902269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348038561/10000000000 : ℝ)^8455 ≤ (33317601531697/100000000000000 : ℝ)^6407 := by
    have hnat : (4348038561 : ℕ)^8455*100000000000000^6407 ≤ 33317601531697^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348038561 10000000000 33317601531697 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475079107/10000000000 : ℝ)^8455 ≤ (4326025204897/12500000000000 : ℝ)^6407 := by
    have hnat : (4475079107 : ℕ)^8455*12500000000000^6407 ≤ 4326025204897^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475079107 10000000000 4326025204897 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844902269/2000000000 : ℝ)^8455 ≤ (3207419680877/10000000000000 : ℝ)^6407 := by
    have hnat : (844902269 : ℕ)^8455*10000000000000^6407 ≤ 3207419680877^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844902269 2000000000 3207419680877 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348038561/10000000000 : ℝ), (4475079107/10000000000 : ℝ), (844902269/2000000000 : ℝ)] ![(33317601531697/100000000000000 : ℝ), (4326025204897/12500000000000 : ℝ), (3207419680877/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348038561/10000000000 : ℝ)|^8455 ≤ (33317601531697/100000000000000 : ℝ)^6407
        have hw : |(4348038561/10000000000 : ℝ)|=(4348038561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475079107/10000000000 : ℝ)|^8455 ≤ (4326025204897/12500000000000 : ℝ)^6407
        have hw : |(4475079107/10000000000 : ℝ)|=(4475079107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844902269/2000000000 : ℝ)|^8455 ≤ (3207419680877/10000000000000 : ℝ)^6407
        have hw : |(844902269/2000000000 : ℝ)|=(844902269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1262_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11499/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14119/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7069/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (287/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7069/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (287/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7069/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (287/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7069/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (287/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7069/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (287/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7069/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (287/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (287/2500 : ℝ) ^ (4227/1024 : ℝ) ≤ (1316758746313923/10000000000000000000 : ℝ) := by
    have hpowers : (287/2500 : ℝ)^4227 ≤ (1316758746313923/10000000000000000000 : ℝ)^1024 := by
      have hnat : (287 : ℕ)^4227*10000000000000000000^1024 ≤ 1316758746313923^1024*2500^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        287 2500 1316758746313923 10000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (287/2500 : ℝ)) (X := (1316758746313923/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7069/50000 : ℝ) ^ (4227/1024 : ℝ) ≤ (3110722774070207/10000000000000000000 : ℝ) := by
    have hpowers : (7069/50000 : ℝ)^4227 ≤ (3110722774070207/10000000000000000000 : ℝ)^1024 := by
      have hnat : (7069 : ℕ)^4227*10000000000000000000^1024 ≤ 3110722774070207^1024*50000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7069 50000 3110722774070207 10000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7069/50000 : ℝ)) (X := (3110722774070207/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001316758746313923/5000000000000000000 : ℝ) ≤ (2000127582346007/2000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (5001316758746313923/5000000000000000000 : ℝ)^1024 ≤ (2000127582346007/2000000000000000 : ℝ)^4227 := by
      have hnat : (5001316758746313923 : ℕ)^1024*2000000000000000^4227 ≤ 2000127582346007^4227*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001316758746313923 5000000000000000000 2000127582346007 2000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000127582346007/2000000000000000 : ℝ)) (X := (5001316758746313923/5000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000442748152038413/1000000000000000000 : ℝ) ≤ (10001072387215149/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (1000442748152038413/1000000000000000000 : ℝ)^1024 ≤ (10001072387215149/10000000000000000 : ℝ)^4227 := by
      have hnat : (1000442748152038413 : ℕ)^1024*10000000000000000^4227 ≤ 10001072387215149^4227*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000442748152038413 1000000000000000000 10001072387215149 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001072387215149/10000000000000000 : ℝ)) (X := (1000442748152038413/1000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003110722774070207/5000000000000000000 : ℝ) ≤ (10001506862700263/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (5003110722774070207/5000000000000000000 : ℝ)^1024 ≤ (10001506862700263/10000000000000000 : ℝ)^4227 := by
      have hnat : (5003110722774070207 : ℕ)^1024*10000000000000000^4227 ≤ 10001506862700263^4227*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003110722774070207 5000000000000000000 10001506862700263 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001506862700263/10000000000000000 : ℝ)) (X := (5003110722774070207/5000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1316758746313923/10000000000000000000 : ℝ) ≤ ((2657172001224021559/2658000000000000000 : ℝ)+2*(217237742557/132900000000000 : ℝ)*(287/2500 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (2657172001224021559/2658000000000000000 : ℝ)+2*(217237742557/132900000000000 : ℝ)*(287/2500 : ℝ)=(2000127582346007/2000000000000000 : ℝ) by norm_num, show 1+2*(1316758746313923/10000000000000000000 : ℝ)=(5001316758746313923/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3110722774070207/10000000000000000000 : ℝ)+(1316758746313923/10000000000000000000 : ℝ) ≤ ((2657172001224021559/2658000000000000000 : ℝ)+(217237742557/132900000000000 : ℝ)*((7069/50000 : ℝ)+(287/2500 : ℝ)))^(4227/1024 : ℝ) := by
    rw [show (2657172001224021559/2658000000000000000 : ℝ)+(217237742557/132900000000000 : ℝ)*((7069/50000 : ℝ)+(287/2500 : ℝ))=(10001072387215149/10000000000000000 : ℝ) by norm_num, show 1+(3110722774070207/10000000000000000000 : ℝ)+(1316758746313923/10000000000000000000 : ℝ)=(1000442748152038413/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3110722774070207/10000000000000000000 : ℝ) ≤ ((2657172001224021559/2658000000000000000 : ℝ)+2*(217237742557/132900000000000 : ℝ)*(7069/50000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (2657172001224021559/2658000000000000000 : ℝ)+2*(217237742557/132900000000000 : ℝ)*(7069/50000 : ℝ)=(10001506862700263/10000000000000000 : ℝ) by norm_num, show 1+2*(3110722774070207/10000000000000000000 : ℝ)=(5003110722774070207/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2657172001224021559/2658000000000000000 : ℝ)*(X 1 0+X 2 0)+(217237742557/132900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (287/2500 : ℝ)) (hi := (7069/50000 : ℝ)) (c := (2657172001224021559/2658000000000000000 : ℝ)) (alpha := (217237742557/132900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2657172001224021559/2658000000000000000 : ℝ)*(X 0 1+X 2 1)+(217237742557/132900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (287/2500 : ℝ)) (hi := (7069/50000 : ℝ)) (c := (2657172001224021559/2658000000000000000 : ℝ)) (alpha := (217237742557/132900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2657172001224021559/2658000000000000000 : ℝ)*(X 0 2+X 1 2)+(217237742557/132900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (287/2500 : ℝ)) (hi := (7069/50000 : ℝ)) (c := (2657172001224021559/2658000000000000000 : ℝ)) (alpha := (217237742557/132900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1055387189/5000000000 : ℝ)*X 0 0+(2695495111/5000000000 : ℝ)*X 0 1+(2633659639/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344242723/10000000000 : ℝ)*X 1 0+(-1086738213/5000000000 : ℝ)*X 1 1+(5267319273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668030341/1250000000 : ℝ)*X 2 0+(5267319273/10000000000 : ℝ)*X 2 1+(-108673821/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087007323/2500000000 : ℝ)*X 0 0+(1055967939/2500000000 : ℝ)*X 0 1+(4475716179/10000000000 : ℝ)*X 0 2+(1087007323/2500000000 : ℝ)*X 1 0+(1055967939/2500000000 : ℝ)*X 1 1+(4475716179/10000000000 : ℝ)*X 1 2+(1087007323/2500000000 : ℝ)*X 2 0+(1055967939/2500000000 : ℝ)*X 2 1+(4475716179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1055389591/5000000000 : ℝ)*X 0 0+(1316907929/2500000000 : ℝ)*X 0 1+(2695338263/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312645321/10000000000 : ℝ)*X 1 0+(-2050119461/10000000000 : ℝ)*X 1 1+(1347669031/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062528951/2000000000 : ℝ)*X 2 0+(107813523/200000000 : ℝ)*X 2 1+(-2050120193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348038561/10000000000 : ℝ)*X 0 0+(4475079107/10000000000 : ℝ)*X 0 1+(844902269/2000000000 : ℝ)*X 0 2+(4348038561/10000000000 : ℝ)*X 1 0+(4475079107/10000000000 : ℝ)*X 1 1+(844902269/2000000000 : ℝ)*X 1 2+(4348038561/10000000000 : ℝ)*X 2 0+(4475079107/10000000000 : ℝ)*X 2 1+(844902269/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8151638714780122986679/2215000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143696001/20000000000000 : ℝ)*(base19) + (673652733/100000000000000 : ℝ)*(base23) + (27999789/100000000000000 : ℝ)*(lower2) + (45178431/50000000000000 : ℝ)*(upper3) + (6369497/10000000000000 : ℝ)*(upper5) + (3014184829568029/50000000000000 : ℝ)*(major0) + (3014184829568029/50000000000000 : ℝ)*(major1) + (3014184829568029/50000000000000 : ℝ)*(major2) + (4042996973412613/50000000000000 : ℝ)*(sp0) + (8086013140736381/100000000000000 : ℝ)*(sp1) + (4043006592781827/50000000000000 : ℝ)*(sp2) + (1985357444455757/50000000000000 : ℝ)*(sp3) + (19912391161/100000000000000 : ℝ)*(sp4) + (2089494187/20000000000000 : ℝ)*(sp7) + (248170333523903/6250000000000 : ℝ)*(f.failure) + (4043006929608193/50000000000000 : ℝ)*(f.sum) + (11831755803679/6645000000000000000000000000 : ℝ)*base66 + (4461248759034263/44300000000000000000000000000000 : ℝ)*base68 + (470236286443565737/44300000000000000000000000000000 : ℝ)*base69 + (259289999757734263/44300000000000000000000000000000 : ℝ)*base72 + (251004318971/6645000000000000000000000000 : ℝ)*base73 + (332264933237865737/44300000000000000000000000000000 : ℝ)*base75 + (412125117108434263/44300000000000000000000000000000 : ℝ)*base78 + (540787532776765737/44300000000000000000000000000000 : ℝ)*base79 + (22814735898161/6645000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1584827/156250000000000000000 : ℝ)*base90 + (1584827/156250000000000000000 : ℝ)*base92 + (1584827/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46026221132257088042594733/4430000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (425528829/25000000000000 : ℝ)*(base19) + (815893719/100000000000000 : ℝ)*(base23) + (1038893/800000000000 : ℝ)*(upper2) + (35957057/12500000000000 : ℝ)*(upper3) + (47497849/25000000000000 : ℝ)*(upper5) + (605904629848329/10000000000000 : ℝ)*(major0) + (605904629848329/10000000000000 : ℝ)*(major1) + (605904629848329/10000000000000 : ℝ)*(major2) + (15363313331/50000000000000 : ℝ)*(sp0) + (22261712809/50000000000000 : ℝ)*(sp1) + (8127130308437629/100000000000000 : ℝ)*(sp4) + (8127114809523357/100000000000000 : ℝ)*(sp5) + (8127160219170571/100000000000000 : ℝ)*(sp6) + (498866401947509/12500000000000 : ℝ)*(sp7) + (498866401947509/12500000000000 : ℝ)*(f.failure) + (812716103506429/10000000000000 : ℝ)*(f.sum) + (1823717239713/110750000000000000000000000 : ℝ)*base66 + (122433559396458363/8860000000000000000000000000000 : ℝ)*base68 + (240379719600738363/8860000000000000000000000000000 : ℝ)*base70 + (41665806227518363/8860000000000000000000000000000 : ℝ)*base72 + (130529595607/88600000000000000000000000 : ℝ)*base74 + (196316964635858363/8860000000000000000000000000000 : ℝ)*base76 + (73907033416358363/8860000000000000000000000000000 : ℝ)*base78 + (60917173509378363/8860000000000000000000000000000 : ℝ)*base80 + (979384941311/443000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (68319/312500000000000000000 : ℝ)*base89 + (68319/312500000000000000000 : ℝ)*base91 + (68319/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1262_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1262_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1262_s7_0 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110786849/10000000000 : ℝ)*x 0 + (2695407827/5000000000 : ℝ)*x 1 + (5267485833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110786849/10000000000 : ℝ)^8455 ≤ (2567631901909/20000000000000 : ℝ)^6407 := by
    have hnat : (2110786849 : ℕ)^8455*20000000000000^6407 ≤ 2567631901909^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110786849 10000000000 2567631901909 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695407827/5000000000 : ℝ)^8455 ≤ (22123189395629/50000000000000 : ℝ)^6407 := by
    have hnat : (2695407827 : ℕ)^8455*50000000000000^6407 ≤ 22123189395629^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695407827 5000000000 22123189395629 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267485833/10000000000 : ℝ)^8455 ≤ (42915461681577/100000000000000 : ℝ)^6407 := by
    have hnat : (5267485833 : ℕ)^8455*100000000000000^6407 ≤ 42915461681577^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267485833 10000000000 42915461681577 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110786849/10000000000 : ℝ), (2695407827/5000000000 : ℝ), (5267485833/10000000000 : ℝ)] ![(2567631901909/20000000000000 : ℝ), (22123189395629/50000000000000 : ℝ), (42915461681577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110786849/10000000000 : ℝ)|^8455 ≤ (2567631901909/20000000000000 : ℝ)^6407
        have hw : |(-2110786849/10000000000 : ℝ)|=(2110786849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695407827/5000000000 : ℝ)|^8455 ≤ (22123189395629/50000000000000 : ℝ)^6407
        have hw : |(2695407827/5000000000 : ℝ)|=(2695407827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267485833/10000000000 : ℝ)|^8455 ≤ (42915461681577/100000000000000 : ℝ)^6407
        have hw : |(5267485833/10000000000 : ℝ)|=(5267485833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s7_1 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336049803/2500000000 : ℝ)*x 0 + (-43466269/200000000 : ℝ)*x 1 + (1053497159/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336049803/2500000000 : ℝ)^8455 ≤ (2733884970049/6250000000000 : ℝ)^6407 := by
    have hnat : (1336049803 : ℕ)^8455*6250000000000^6407 ≤ 2733884970049^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336049803 2500000000 2733884970049 6250000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43466269/200000000 : ℝ)^8455 ≤ (13342379189077/100000000000000 : ℝ)^6407 := by
    have hnat : (43466269 : ℕ)^8455*100000000000000^6407 ≤ 13342379189077^6407*200000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43466269 200000000 13342379189077 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053497159/2000000000 : ℝ)^8455 ≤ (42915461273019/100000000000000 : ℝ)^6407 := by
    have hnat : (1053497159 : ℕ)^8455*100000000000000^6407 ≤ 42915461273019^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053497159 2000000000 42915461273019 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336049803/2500000000 : ℝ), (-43466269/200000000 : ℝ), (1053497159/2000000000 : ℝ)] ![(2733884970049/6250000000000 : ℝ), (13342379189077/100000000000000 : ℝ), (42915461273019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336049803/2500000000 : ℝ)|^8455 ≤ (2733884970049/6250000000000 : ℝ)^6407
        have hw : |(1336049803/2500000000 : ℝ)|=(1336049803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43466269/200000000 : ℝ)|^8455 ≤ (13342379189077/100000000000000 : ℝ)^6407
        have hw : |(-43466269/200000000 : ℝ)|=(43466269/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053497159/2000000000 : ℝ)|^8455 ≤ (42915461273019/100000000000000 : ℝ)^6407
        have hw : |(1053497159/2000000000 : ℝ)|=(1053497159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s7_2 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672099553/5000000000 : ℝ)*x 0 + (5267486003/10000000000 : ℝ)*x 1 + (-543328329/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672099553/5000000000 : ℝ)^8455 ≤ (8748431675169/20000000000000 : ℝ)^6407 := by
    have hnat : (2672099553 : ℕ)^8455*20000000000000^6407 ≤ 8748431675169^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672099553 5000000000 8748431675169 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267486003/10000000000 : ℝ)^8455 ≤ (42915463509333/100000000000000 : ℝ)^6407 := by
    have hnat : (5267486003 : ℕ)^8455*100000000000000^6407 ≤ 42915463509333^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267486003 10000000000 42915463509333 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543328329/2500000000 : ℝ)^8455 ≤ (6671189051733/50000000000000 : ℝ)^6407 := by
    have hnat : (543328329 : ℕ)^8455*50000000000000^6407 ≤ 6671189051733^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543328329 2500000000 6671189051733 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672099553/5000000000 : ℝ), (5267486003/10000000000 : ℝ), (-543328329/2500000000 : ℝ)] ![(8748431675169/20000000000000 : ℝ), (42915463509333/100000000000000 : ℝ), (6671189051733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672099553/5000000000 : ℝ)|^8455 ≤ (8748431675169/20000000000000 : ℝ)^6407
        have hw : |(2672099553/5000000000 : ℝ)|=(2672099553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267486003/10000000000 : ℝ)|^8455 ≤ (42915463509333/100000000000000 : ℝ)^6407
        have hw : |(5267486003/10000000000 : ℝ)|=(5267486003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-543328329/2500000000 : ℝ)|^8455 ≤ (6671189051733/50000000000000 : ℝ)^6407
        have hw : |(-543328329/2500000000 : ℝ)|=(543328329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s7_3 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348038039/10000000000 : ℝ)*x 0 + (1056054527/2500000000 : ℝ)*x 1 + (279710469/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348038039/10000000000 : ℝ)^8455 ≤ (33317596253207/100000000000000 : ℝ)^6407 := by
    have hnat : (4348038039 : ℕ)^8455*100000000000000^6407 ≤ 33317596253207^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348038039 10000000000 33317596253207 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056054527/2500000000 : ℝ)^8455 ≤ (1002226837699/3125000000000 : ℝ)^6407 := by
    have hnat : (1056054527 : ℕ)^8455*3125000000000^6407 ≤ 1002226837699^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056054527 2500000000 1002226837699 3125000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279710469/625000000 : ℝ)^8455 ≤ (865278623121/2500000000000 : ℝ)^6407 := by
    have hnat : (279710469 : ℕ)^8455*2500000000000^6407 ≤ 865278623121^6407*625000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279710469 625000000 865278623121 2500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348038039/10000000000 : ℝ), (1056054527/2500000000 : ℝ), (279710469/625000000 : ℝ)] ![(33317596253207/100000000000000 : ℝ), (1002226837699/3125000000000 : ℝ), (865278623121/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348038039/10000000000 : ℝ)|^8455 ≤ (33317596253207/100000000000000 : ℝ)^6407
        have hw : |(4348038039/10000000000 : ℝ)|=(4348038039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056054527/2500000000 : ℝ)|^8455 ≤ (1002226837699/3125000000000 : ℝ)^6407
        have hw : |(1056054527/2500000000 : ℝ)|=(1056054527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(279710469/625000000 : ℝ)|^8455 ≤ (865278623121/2500000000000 : ℝ)^6407
        have hw : |(279710469/625000000 : ℝ)|=(279710469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s7_4 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110791483/10000000000 : ℝ)*x 0 + (5267797051/10000000000 : ℝ)*x 1 + (539050329/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110791483/10000000000 : ℝ)^8455 ≤ (6419098351797/50000000000000 : ℝ)^6407 := by
    have hnat : (2110791483 : ℕ)^8455*50000000000000^6407 ≤ 6419098351797^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110791483 10000000000 6419098351797 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267797051/10000000000 : ℝ)^8455 ≤ (67060637149/156250000000 : ℝ)^6407 := by
    have hnat : (5267797051 : ℕ)^8455*156250000000^6407 ≤ 67060637149^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267797051 10000000000 67060637149 156250000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539050329/1000000000 : ℝ)^8455 ≤ (44242995502281/100000000000000 : ℝ)^6407 := by
    have hnat : (539050329 : ℕ)^8455*100000000000000^6407 ≤ 44242995502281^6407*1000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539050329 1000000000 44242995502281 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110791483/10000000000 : ℝ), (5267797051/10000000000 : ℝ), (539050329/1000000000 : ℝ)] ![(6419098351797/50000000000000 : ℝ), (67060637149/156250000000 : ℝ), (44242995502281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110791483/10000000000 : ℝ)|^8455 ≤ (6419098351797/50000000000000 : ℝ)^6407
        have hw : |(-2110791483/10000000000 : ℝ)|=(2110791483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267797051/10000000000 : ℝ)|^8455 ≤ (67060637149/156250000000 : ℝ)^6407
        have hw : |(5267797051/10000000000 : ℝ)|=(5267797051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539050329/1000000000 : ℝ)|^8455 ≤ (44242995502281/100000000000000 : ℝ)^6407
        have hw : |(539050329/1000000000 : ℝ)|=(539050329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s7_5 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062537769/2000000000 : ℝ)*x 0 + (-2050296027/10000000000 : ℝ)*x 1 + (5390503171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062537769/2000000000 : ℝ)^8455 ≤ (10850531853229/25000000000000 : ℝ)^6407 := by
    have hnat : (1062537769 : ℕ)^8455*25000000000000^6407 ≤ 10850531853229^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062537769 2000000000 10850531853229 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050296027/10000000000 : ℝ)^8455 ≤ (494195134069/4000000000000 : ℝ)^6407 := by
    have hnat : (2050296027 : ℕ)^8455*4000000000000^6407 ≤ 494195134069^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050296027 10000000000 494195134069 4000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390503171/10000000000 : ℝ)^8455 ≤ (86412098073/195312500000 : ℝ)^6407 := by
    have hnat : (5390503171 : ℕ)^8455*195312500000^6407 ≤ 86412098073^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390503171 10000000000 86412098073 195312500000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062537769/2000000000 : ℝ), (-2050296027/10000000000 : ℝ), (5390503171/10000000000 : ℝ)] ![(10850531853229/25000000000000 : ℝ), (494195134069/4000000000000 : ℝ), (86412098073/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062537769/2000000000 : ℝ)|^8455 ≤ (10850531853229/25000000000000 : ℝ)^6407
        have hw : |(1062537769/2000000000 : ℝ)|=(1062537769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050296027/10000000000 : ℝ)|^8455 ≤ (494195134069/4000000000000 : ℝ)^6407
        have hw : |(-2050296027/10000000000 : ℝ)|=(2050296027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390503171/10000000000 : ℝ)|^8455 ≤ (86412098073/195312500000 : ℝ)^6407
        have hw : |(5390503171/10000000000 : ℝ)|=(5390503171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s7_6 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166021527/312500000 : ℝ)*x 0 + (5390503161/10000000000 : ℝ)*x 1 + (-410059203/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166021527/312500000 : ℝ)^8455 ≤ (21701063808877/50000000000000 : ℝ)^6407 := by
    have hnat : (166021527 : ℕ)^8455*50000000000000^6407 ≤ 21701063808877^6407*312500000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166021527 312500000 21701063808877 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390503161/10000000000 : ℝ)^8455 ≤ (5530374263133/12500000000000 : ℝ)^6407 := by
    have hnat : (5390503161 : ℕ)^8455*12500000000000^6407 ≤ 5530374263133^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390503161 10000000000 5530374263133 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410059203/2000000000 : ℝ)^8455 ≤ (123548782563/1000000000000 : ℝ)^6407 := by
    have hnat : (410059203 : ℕ)^8455*1000000000000^6407 ≤ 123548782563^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410059203 2000000000 123548782563 1000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166021527/312500000 : ℝ), (5390503161/10000000000 : ℝ), (-410059203/2000000000 : ℝ)] ![(21701063808877/50000000000000 : ℝ), (5530374263133/12500000000000 : ℝ), (123548782563/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166021527/312500000 : ℝ)|^8455 ≤ (21701063808877/50000000000000 : ℝ)^6407
        have hw : |(166021527/312500000 : ℝ)|=(166021527/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390503161/10000000000 : ℝ)|^8455 ≤ (5530374263133/12500000000000 : ℝ)^6407
        have hw : |(5390503161/10000000000 : ℝ)|=(5390503161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410059203/2000000000 : ℝ)|^8455 ≤ (123548782563/1000000000000 : ℝ)^6407
        have hw : |(-410059203/2000000000 : ℝ)|=(410059203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s7_7 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174023641/5000000000 : ℝ)*x 0 + (1118683463/2500000000 : ℝ)*x 1 + (66013347/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174023641/5000000000 : ℝ)^8455 ≤ (16658844859459/50000000000000 : ℝ)^6407 := by
    have hnat : (2174023641 : ℕ)^8455*50000000000000^6407 ≤ 16658844859459^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174023641 5000000000 16658844859459 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118683463/2500000000 : ℝ)^8455 ≤ (1730233907953/5000000000000 : ℝ)^6407 := by
    have hnat : (1118683463 : ℕ)^8455*5000000000000^6407 ≤ 1730233907953^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118683463 2500000000 1730233907953 5000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66013347/156250000 : ℝ)^8455 ≤ (16038816053521/50000000000000 : ℝ)^6407 := by
    have hnat : (66013347 : ℕ)^8455*50000000000000^6407 ≤ 16038816053521^6407*156250000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66013347 156250000 16038816053521 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174023641/5000000000 : ℝ), (1118683463/2500000000 : ℝ), (66013347/156250000 : ℝ)] ![(16658844859459/50000000000000 : ℝ), (1730233907953/5000000000000 : ℝ), (16038816053521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174023641/5000000000 : ℝ)|^8455 ≤ (16658844859459/50000000000000 : ℝ)^6407
        have hw : |(2174023641/5000000000 : ℝ)|=(2174023641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118683463/2500000000 : ℝ)|^8455 ≤ (1730233907953/5000000000000 : ℝ)^6407
        have hw : |(1118683463/2500000000 : ℝ)|=(1118683463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66013347/156250000 : ℝ)|^8455 ≤ (16038816053521/50000000000000 : ℝ)^6407
        have hw : |(66013347/156250000 : ℝ)|=(66013347/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1262_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5751/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2823/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11499/100000 : ℝ) ^ (4227/1024 : ℝ) ≤ (6628890376364389/50000000000000000000 : ℝ) := by
    have hpowers : (11499/100000 : ℝ)^4227 ≤ (6628890376364389/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11499 : ℕ)^4227*50000000000000000000^1024 ≤ 6628890376364389^1024*100000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11499 100000 6628890376364389 50000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11499/100000 : ℝ)) (X := (6628890376364389/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14119/100000 : ℝ) ^ (4227/1024 : ℝ) ≤ (15467511256402873/50000000000000000000 : ℝ) := by
    have hpowers : (14119/100000 : ℝ)^4227 ≤ (15467511256402873/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14119 : ℕ)^4227*50000000000000000000^1024 ≤ 15467511256402873^1024*100000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14119 100000 15467511256402873 50000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14119/100000 : ℝ)) (X := (15467511256402873/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006628890376364389/25000000000000000000 : ℝ) ≤ (10000642280759573/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (25006628890376364389/25000000000000000000 : ℝ)^1024 ≤ (10000642280759573/10000000000000000 : ℝ)^4227 := by
      have hnat : (25006628890376364389 : ℕ)^1024*10000000000000000^4227 ≤ 10000642280759573^4227*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006628890376364389 25000000000000000000 10000642280759573 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000642280759573/10000000000000000 : ℝ)) (X := (25006628890376364389/25000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011048200816383631/25000000000000000000 : ℝ) ≤ (10001070401123661/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (25011048200816383631/25000000000000000000 : ℝ)^1024 ≤ (10001070401123661/10000000000000000 : ℝ)^4227 := by
      have hnat : (25011048200816383631 : ℕ)^1024*10000000000000000^4227 ≤ 10001070401123661^4227*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011048200816383631 25000000000000000000 10001070401123661 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001070401123661/10000000000000000 : ℝ)) (X := (25011048200816383631/25000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015467511256402873/25000000000000000000 : ℝ) ≤ (10001498521487749/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (25015467511256402873/25000000000000000000 : ℝ)^1024 ≤ (10001498521487749/10000000000000000 : ℝ)^4227 := by
      have hnat : (25015467511256402873 : ℕ)^1024*10000000000000000^4227 ≤ 10001498521487749^4227*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015467511256402873 25000000000000000000 10001498521487749 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001498521487749/10000000000000000 : ℝ)) (X := (25015467511256402873/25000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6628890376364389/50000000000000000000 : ℝ) ≤ ((6547959215864196359/6550000000000000000 : ℝ)+2*(53515045511/32750000000000 : ℝ)*(11499/100000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (6547959215864196359/6550000000000000000 : ℝ)+2*(53515045511/32750000000000 : ℝ)*(11499/100000 : ℝ)=(10000642280759573/10000000000000000 : ℝ) by norm_num, show 1+2*(6628890376364389/50000000000000000000 : ℝ)=(25006628890376364389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15467511256402873/50000000000000000000 : ℝ)+(6628890376364389/50000000000000000000 : ℝ) ≤ ((6547959215864196359/6550000000000000000 : ℝ)+(53515045511/32750000000000 : ℝ)*((14119/100000 : ℝ)+(11499/100000 : ℝ)))^(4227/1024 : ℝ) := by
    rw [show (6547959215864196359/6550000000000000000 : ℝ)+(53515045511/32750000000000 : ℝ)*((14119/100000 : ℝ)+(11499/100000 : ℝ))=(10001070401123661/10000000000000000 : ℝ) by norm_num, show 1+(15467511256402873/50000000000000000000 : ℝ)+(6628890376364389/50000000000000000000 : ℝ)=(25011048200816383631/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15467511256402873/50000000000000000000 : ℝ) ≤ ((6547959215864196359/6550000000000000000 : ℝ)+2*(53515045511/32750000000000 : ℝ)*(14119/100000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (6547959215864196359/6550000000000000000 : ℝ)+2*(53515045511/32750000000000 : ℝ)*(14119/100000 : ℝ)=(10001498521487749/10000000000000000 : ℝ) by norm_num, show 1+2*(15467511256402873/50000000000000000000 : ℝ)=(25015467511256402873/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6547959215864196359/6550000000000000000 : ℝ)*(X 1 0+X 2 0)+(53515045511/32750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (11499/100000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (6547959215864196359/6550000000000000000 : ℝ)) (alpha := (53515045511/32750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6547959215864196359/6550000000000000000 : ℝ)*(X 0 1+X 2 1)+(53515045511/32750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (11499/100000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (6547959215864196359/6550000000000000000 : ℝ)) (alpha := (53515045511/32750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6547959215864196359/6550000000000000000 : ℝ)*(X 0 2+X 1 2)+(53515045511/32750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (11499/100000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (6547959215864196359/6550000000000000000 : ℝ)) (alpha := (53515045511/32750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2110786849/10000000000 : ℝ)*X 0 0+(2695407827/5000000000 : ℝ)*X 0 1+(5267485833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336049803/2500000000 : ℝ)*X 1 0+(-43466269/200000000 : ℝ)*X 1 1+(1053497159/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672099553/5000000000 : ℝ)*X 2 0+(5267486003/10000000000 : ℝ)*X 2 1+(-543328329/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348038039/10000000000 : ℝ)*X 0 0+(1056054527/2500000000 : ℝ)*X 0 1+(279710469/625000000 : ℝ)*X 0 2+(4348038039/10000000000 : ℝ)*X 1 0+(1056054527/2500000000 : ℝ)*X 1 1+(279710469/625000000 : ℝ)*X 1 2+(4348038039/10000000000 : ℝ)*X 2 0+(1056054527/2500000000 : ℝ)*X 2 1+(279710469/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2110791483/10000000000 : ℝ)*X 0 0+(5267797051/10000000000 : ℝ)*X 0 1+(539050329/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062537769/2000000000 : ℝ)*X 1 0+(-2050296027/10000000000 : ℝ)*X 1 1+(5390503171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166021527/312500000 : ℝ)*X 2 0+(5390503161/10000000000 : ℝ)*X 2 1+(-410059203/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174023641/5000000000 : ℝ)*X 0 0+(1118683463/2500000000 : ℝ)*X 0 1+(66013347/156250000 : ℝ)*X 0 2+(2174023641/5000000000 : ℝ)*X 1 0+(1118683463/2500000000 : ℝ)*X 1 1+(66013347/156250000 : ℝ)*X 1 2+(2174023641/5000000000 : ℝ)*X 2 0+(1118683463/2500000000 : ℝ)*X 2 1+(66013347/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (644715356531691758542965333/81875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2058598351/100000000000000 : ℝ)*(base19) + (1790163667/100000000000000 : ℝ)*(base23) + (57507177/100000000000000 : ℝ)*(lower2) + (156871987/100000000000000 : ℝ)*(upper3) + (271618763/100000000000000 : ℝ)*(upper5) + (1511276131232671/25000000000000 : ℝ)*(major0) + (1511276131232671/25000000000000 : ℝ)*(major1) + (1511276131232671/25000000000000 : ℝ)*(major2) + (4054198352913413/50000000000000 : ℝ)*(sp0) + (4054229292672779/50000000000000 : ℝ)*(sp1) + (4054229426890121/50000000000000 : ℝ)*(sp2) + (1990861101491151/50000000000000 : ℝ)*(sp3) + (63938117083/100000000000000 : ℝ)*(sp4) + (6485113903/25000000000000 : ℝ)*(sp7) + (1990874071718957/50000000000000 : ℝ)*(f.failure) + (8108460643943909/100000000000000 : ℝ)*(f.sum) + (8073440047323/3275000000000000000000000000 : ℝ)*base65 + (45222962827494889/163750000000000000000000000000000 : ℝ)*base67 + (1435720600053755111/163750000000000000000000000000000 : ℝ)*base70 + (3419033940688744889/163750000000000000000000000000000 : ℝ)*base71 + (2968167372637/818750000000000000000000000 : ℝ)*base73 + (634703002731255111/163750000000000000000000000000000 : ℝ)*base76 + (437872941143744889/163750000000000000000000000000000 : ℝ)*base77 + (2429603695503744889/163750000000000000000000000000000 : ℝ)*base79 + (137671853041/25585937500000000000000000 : ℝ)*base81 + (10639913/1250000000000000000000 : ℝ)*base90 + (10639913/1250000000000000000000 : ℝ)*base92 + (10639913/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (342749553389767944313621863/81875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1414993449/100000000000000 : ℝ)*(base19) + (1530040429/100000000000000 : ℝ)*(base23) + (45947769/100000000000000 : ℝ)*(upper2) + (38023759/50000000000000 : ℝ)*(upper3) + (162431573/100000000000000 : ℝ)*(upper5) + (3037868209692781/50000000000000 : ℝ)*(major0) + (3037868209692781/50000000000000 : ℝ)*(major1) + (3037868209692781/50000000000000 : ℝ)*(major2) + (3895495537/10000000000000 : ℝ)*(sp1) + (38856403587/100000000000000 : ℝ)*(sp2) + (4074774074426867/50000000000000 : ℝ)*(sp4) + (2037376944726229/25000000000000 : ℝ)*(sp5) + (4074753881204859/50000000000000 : ℝ)*(sp6) + (160076982015023/4000000000000 : ℝ)*(sp7) + (160076982015023/4000000000000 : ℝ)*(f.failure) + (4074774074426867/50000000000000 : ℝ)*(f.sum) + (352217925917/409375000000000000000000000 : ℝ)*base66 + (3656878554181984379/327500000000000000000000000000000 : ℝ)*base67 + (2704000560416984379/327500000000000000000000000000000 : ℝ)*base69 + (4210594503791984379/327500000000000000000000000000000 : ℝ)*base71 + (5420638597/6396484375000000000000000 : ℝ)*base73 + (3873402322848015621/327500000000000000000000000000000 : ℝ)*base76 + (3147351633956984379/327500000000000000000000000000000 : ℝ)*base77 + (5522949671244484379/327500000000000000000000000000000 : ℝ)*base79 + (8594219996207/1637500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (667907/100000000000000000000 : ℝ)*base90 + (667907/100000000000000000000 : ℝ)*base92 + (667907/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1262_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5751/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1262_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1262_s8_0 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-211079201/1000000000 : ℝ)*x 0 + (539078227/1000000000 : ℝ)*x 1 + (5267515611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211079201/1000000000 : ℝ)^8455 ≤ (3209550233369/25000000000000 : ℝ)^6407 := by
    have hnat : (211079201 : ℕ)^8455*25000000000000^6407 ≤ 3209550233369^6407*1000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211079201 1000000000 3209550233369 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539078227/1000000000 : ℝ)^8455 ≤ (44246017198201/100000000000000 : ℝ)^6407 := by
    have hnat : (539078227 : ℕ)^8455*100000000000000^6407 ≤ 44246017198201^6407*1000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539078227 1000000000 44246017198201 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267515611/10000000000 : ℝ)^8455 ≤ (42915781840211/100000000000000 : ℝ)^6407 := by
    have hnat : (5267515611 : ℕ)^8455*100000000000000^6407 ≤ 42915781840211^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267515611 10000000000 42915781840211 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211079201/1000000000 : ℝ), (539078227/1000000000 : ℝ), (5267515611/10000000000 : ℝ)] ![(3209550233369/25000000000000 : ℝ), (44246017198201/100000000000000 : ℝ), (42915781840211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211079201/1000000000 : ℝ)|^8455 ≤ (3209550233369/25000000000000 : ℝ)^6407
        have hw : |(-211079201/1000000000 : ℝ)|=(211079201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539078227/1000000000 : ℝ)|^8455 ≤ (44246017198201/100000000000000 : ℝ)^6407
        have hw : |(539078227/1000000000 : ℝ)|=(539078227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267515611/10000000000 : ℝ)|^8455 ≤ (42915781840211/100000000000000 : ℝ)^6407
        have hw : |(5267515611/10000000000 : ℝ)|=(5267515611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s8_1 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534418993/1000000000 : ℝ)*x 0 + (-434657251/2000000000 : ℝ)*x 1 + (5267515613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534418993/1000000000 : ℝ)^8455 ≤ (43742059263043/100000000000000 : ℝ)^6407 := by
    have hnat : (534418993 : ℕ)^8455*100000000000000^6407 ≤ 43742059263043^6407*1000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534418993 1000000000 43742059263043 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434657251/2000000000 : ℝ)^8455 ≤ (3335539716753/25000000000000 : ℝ)^6407 := by
    have hnat : (434657251 : ℕ)^8455*25000000000000^6407 ≤ 3335539716753^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434657251 2000000000 3335539716753 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267515613/10000000000 : ℝ)^8455 ≤ (21457890930857/50000000000000 : ℝ)^6407 := by
    have hnat : (5267515613 : ℕ)^8455*50000000000000^6407 ≤ 21457890930857^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267515613 10000000000 21457890930857 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534418993/1000000000 : ℝ), (-434657251/2000000000 : ℝ), (5267515613/10000000000 : ℝ)] ![(43742059263043/100000000000000 : ℝ), (3335539716753/25000000000000 : ℝ), (21457890930857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534418993/1000000000 : ℝ)|^8455 ≤ (43742059263043/100000000000000 : ℝ)^6407
        have hw : |(534418993/1000000000 : ℝ)|=(534418993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434657251/2000000000 : ℝ)|^8455 ≤ (3335539716753/25000000000000 : ℝ)^6407
        have hw : |(-434657251/2000000000 : ℝ)|=(434657251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267515613/10000000000 : ℝ)|^8455 ≤ (21457890930857/50000000000000 : ℝ)^6407
        have hw : |(5267515613/10000000000 : ℝ)|=(5267515613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s8_2 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344189927/10000000000 : ℝ)*x 0 + (5267515613/10000000000 : ℝ)*x 1 + (-2173286257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344189927/10000000000 : ℝ)^8455 ≤ (43742059230639/100000000000000 : ℝ)^6407 := by
    have hnat : (5344189927 : ℕ)^8455*100000000000000^6407 ≤ 43742059230639^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344189927 10000000000 43742059230639 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267515613/10000000000 : ℝ)^8455 ≤ (21457890930857/50000000000000 : ℝ)^6407 := by
    have hnat : (5267515613 : ℕ)^8455*50000000000000^6407 ≤ 21457890930857^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267515613 10000000000 21457890930857 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2173286257/10000000000 : ℝ)^8455 ≤ (2668431776643/20000000000000 : ℝ)^6407 := by
    have hnat : (2173286257 : ℕ)^8455*20000000000000^6407 ≤ 2668431776643^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173286257 10000000000 2668431776643 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344189927/10000000000 : ℝ), (5267515613/10000000000 : ℝ), (-2173286257/10000000000 : ℝ)] ![(43742059230639/100000000000000 : ℝ), (21457890930857/50000000000000 : ℝ), (2668431776643/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344189927/10000000000 : ℝ)|^8455 ≤ (43742059230639/100000000000000 : ℝ)^6407
        have hw : |(5344189927/10000000000 : ℝ)|=(5344189927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267515613/10000000000 : ℝ)|^8455 ≤ (21457890930857/50000000000000 : ℝ)^6407
        have hw : |(5267515613/10000000000 : ℝ)|=(5267515613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2173286257/10000000000 : ℝ)|^8455 ≤ (2668431776643/20000000000000 : ℝ)^6407
        have hw : |(-2173286257/10000000000 : ℝ)|=(2173286257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s8_3 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174019747/5000000000 : ℝ)*x 0 + (4224282111/10000000000 : ℝ)*x 1 + (447530323/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174019747/5000000000 : ℝ)^8455 ≤ (33317610966241/100000000000000 : ℝ)^6407 := by
    have hnat : (2174019747 : ℕ)^8455*100000000000000^6407 ≤ 33317610966241^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174019747 5000000000 33317610966241 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224282111/10000000000 : ℝ)^8455 ≤ (6414380012031/20000000000000 : ℝ)^6407 := by
    have hnat : (4224282111 : ℕ)^8455*20000000000000^6407 ≤ 6414380012031^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224282111 10000000000 6414380012031 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447530323/1000000000 : ℝ)^8455 ≤ (17305244480061/50000000000000 : ℝ)^6407 := by
    have hnat : (447530323 : ℕ)^8455*50000000000000^6407 ≤ 17305244480061^6407*1000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447530323 1000000000 17305244480061 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174019747/5000000000 : ℝ), (4224282111/10000000000 : ℝ), (447530323/1000000000 : ℝ)] ![(33317610966241/100000000000000 : ℝ), (6414380012031/20000000000000 : ℝ), (17305244480061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174019747/5000000000 : ℝ)|^8455 ≤ (33317610966241/100000000000000 : ℝ)^6407
        have hw : |(2174019747/5000000000 : ℝ)|=(2174019747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224282111/10000000000 : ℝ)|^8455 ≤ (6414380012031/20000000000000 : ℝ)^6407
        have hw : |(4224282111/10000000000 : ℝ)|=(4224282111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447530323/1000000000 : ℝ)|^8455 ≤ (17305244480061/50000000000000 : ℝ)^6407
        have hw : |(447530323/1000000000 : ℝ)|=(447530323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s8_4 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110796581/10000000000 : ℝ)*x 0 + (2633913279/5000000000 : ℝ)*x 1 + (2695235111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110796581/10000000000 : ℝ)^8455 ≤ (6419118810947/50000000000000 : ℝ)^6407 := by
    have hnat : (2110796581 : ℕ)^8455*50000000000000^6407 ≤ 6419118810947^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110796581 10000000000 6419118810947 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633913279/5000000000 : ℝ)^8455 ≤ (21459562513161/50000000000000 : ℝ)^6407 := by
    have hnat : (2633913279 : ℕ)^8455*50000000000000^6407 ≤ 21459562513161^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633913279 5000000000 21459562513161 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695235111/5000000000 : ℝ)^8455 ≤ (8848527467711/20000000000000 : ℝ)^6407 := by
    have hnat : (2695235111 : ℕ)^8455*20000000000000^6407 ≤ 8848527467711^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695235111 5000000000 8848527467711 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110796581/10000000000 : ℝ), (2633913279/5000000000 : ℝ), (2695235111/5000000000 : ℝ)] ![(6419118810947/50000000000000 : ℝ), (21459562513161/50000000000000 : ℝ), (8848527467711/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110796581/10000000000 : ℝ)|^8455 ≤ (6419118810947/50000000000000 : ℝ)^6407
        have hw : |(-2110796581/10000000000 : ℝ)|=(2110796581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633913279/5000000000 : ℝ)|^8455 ≤ (21459562513161/50000000000000 : ℝ)^6407
        have hw : |(2633913279/5000000000 : ℝ)|=(2633913279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695235111/5000000000 : ℝ)|^8455 ≤ (8848527467711/20000000000000 : ℝ)^6407
        have hw : |(2695235111/5000000000 : ℝ)|=(2695235111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s8_5 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212507827/400000000 : ℝ)*x 0 + (-1025165801/5000000000 : ℝ)*x 1 + (2695235127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212507827/400000000 : ℝ)^8455 ≤ (10850550261641/25000000000000 : ℝ)^6407 := by
    have hnat : (212507827 : ℕ)^8455*25000000000000^6407 ≤ 10850550261641^6407*400000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212507827 400000000 10850550261641 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025165801/5000000000 : ℝ)^8455 ≤ (12355161247789/100000000000000 : ℝ)^6407 := by
    have hnat : (1025165801 : ℕ)^8455*100000000000000^6407 ≤ 12355161247789^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025165801 5000000000 12355161247789 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695235127/5000000000 : ℝ)^8455 ≤ (44242637685151/100000000000000 : ℝ)^6407 := by
    have hnat : (2695235127 : ℕ)^8455*100000000000000^6407 ≤ 44242637685151^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695235127 5000000000 44242637685151 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212507827/400000000 : ℝ), (-1025165801/5000000000 : ℝ), (2695235127/5000000000 : ℝ)] ![(10850550261641/25000000000000 : ℝ), (12355161247789/100000000000000 : ℝ), (44242637685151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212507827/400000000 : ℝ)|^8455 ≤ (10850550261641/25000000000000 : ℝ)^6407
        have hw : |(212507827/400000000 : ℝ)|=(212507827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025165801/5000000000 : ℝ)|^8455 ≤ (12355161247789/100000000000000 : ℝ)^6407
        have hw : |(-1025165801/5000000000 : ℝ)|=(1025165801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695235127/5000000000 : ℝ)|^8455 ≤ (44242637685151/100000000000000 : ℝ)^6407
        have hw : |(2695235127/5000000000 : ℝ)|=(2695235127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s8_6 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656347843/5000000000 : ℝ)*x 0 + (5390470251/10000000000 : ℝ)*x 1 + (-256291449/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656347843/5000000000 : ℝ)^8455 ≤ (21701100582577/50000000000000 : ℝ)^6407 := by
    have hnat : (2656347843 : ℕ)^8455*50000000000000^6407 ≤ 21701100582577^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656347843 5000000000 21701100582577 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390470251/10000000000 : ℝ)^8455 ≤ (22121318826329/50000000000000 : ℝ)^6407 := by
    have hnat : (5390470251 : ℕ)^8455*50000000000000^6407 ≤ 22121318826329^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390470251 10000000000 22121318826329 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256291449/1250000000 : ℝ)^8455 ≤ (12355161168267/100000000000000 : ℝ)^6407 := by
    have hnat : (256291449 : ℕ)^8455*100000000000000^6407 ≤ 12355161168267^6407*1250000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256291449 1250000000 12355161168267 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656347843/5000000000 : ℝ), (5390470251/10000000000 : ℝ), (-256291449/1250000000 : ℝ)] ![(21701100582577/50000000000000 : ℝ), (22121318826329/50000000000000 : ℝ), (12355161168267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656347843/5000000000 : ℝ)|^8455 ≤ (21701100582577/50000000000000 : ℝ)^6407
        have hw : |(2656347843/5000000000 : ℝ)|=(2656347843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390470251/10000000000 : ℝ)|^8455 ≤ (22121318826329/50000000000000 : ℝ)^6407
        have hw : |(5390470251/10000000000 : ℝ)|=(5390470251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256291449/1250000000 : ℝ)|^8455 ≤ (12355161168267/100000000000000 : ℝ)^6407
        have hw : |(-256291449/1250000000 : ℝ)|=(256291449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s8_7 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543506109/1250000000 : ℝ)*x 0 + (1118667529/2500000000 : ℝ)*x 1 + (4224917521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543506109/1250000000 : ℝ)^8455 ≤ (33317705797089/100000000000000 : ℝ)^6407 := by
    have hnat : (543506109 : ℕ)^8455*100000000000000^6407 ≤ 33317705797089^6407*1250000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543506109 1250000000 33317705797089 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118667529/2500000000 : ℝ)^8455 ≤ (17302013857233/50000000000000 : ℝ)^6407 := by
    have hnat : (1118667529 : ℕ)^8455*50000000000000^6407 ≤ 17302013857233^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118667529 2500000000 17302013857233 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224917521/10000000000 : ℝ)^8455 ≤ (4009783309769/12500000000000 : ℝ)^6407 := by
    have hnat : (4224917521 : ℕ)^8455*12500000000000^6407 ≤ 4009783309769^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224917521 10000000000 4009783309769 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543506109/1250000000 : ℝ), (1118667529/2500000000 : ℝ), (4224917521/10000000000 : ℝ)] ![(33317705797089/100000000000000 : ℝ), (17302013857233/50000000000000 : ℝ), (4009783309769/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543506109/1250000000 : ℝ)|^8455 ≤ (33317705797089/100000000000000 : ℝ)^6407
        have hw : |(543506109/1250000000 : ℝ)|=(543506109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118667529/2500000000 : ℝ)|^8455 ≤ (17302013857233/50000000000000 : ℝ)^6407
        have hw : |(1118667529/2500000000 : ℝ)|=(1118667529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224917521/10000000000 : ℝ)|^8455 ≤ (4009783309769/12500000000000 : ℝ)^6407
        have hw : |(4224917521/10000000000 : ℝ)|=(4224917521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1262_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5751/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11503/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7057/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2823/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5751/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5751/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5751/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5751/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5751/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5751/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5751/50000 : ℝ) ^ (4227/1024 : ℝ) ≤ (6636032239268663/50000000000000000000 : ℝ) := by
    have hpowers : (5751/50000 : ℝ)^4227 ≤ (6636032239268663/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5751 : ℕ)^4227*50000000000000000000^1024 ≤ 6636032239268663^1024*50000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5751 50000 6636032239268663 50000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5751/50000 : ℝ)) (X := (6636032239268663/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2823/20000 : ℝ) ^ (4227/1024 : ℝ) ≤ (30898861020117819/100000000000000000000 : ℝ) := by
    have hpowers : (2823/20000 : ℝ)^4227 ≤ (30898861020117819/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2823 : ℕ)^4227*100000000000000000000^1024 ≤ 30898861020117819^1024*20000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 20000 30898861020117819 100000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/20000 : ℝ)) (X := (30898861020117819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006636032239268663/25000000000000000000 : ℝ) ≤ (40002571890693/40000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (25006636032239268663/25000000000000000000 : ℝ)^1024 ≤ (40002571890693/40000000000000 : ℝ)^4227 := by
      have hnat : (25006636032239268663 : ℕ)^1024*40000000000000^4227 ≤ 40002571890693^4227*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006636032239268663 25000000000000000000 40002571890693 40000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40002571890693/40000000000000 : ℝ)) (X := (25006636032239268663/25000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008834185099731029/20000000000000000000 : ℝ) ≤ (10001069871307337/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (20008834185099731029/20000000000000000000 : ℝ)^1024 ≤ (10001069871307337/10000000000000000 : ℝ)^4227 := by
      have hnat : (20008834185099731029 : ℕ)^1024*10000000000000000^4227 ≤ 10001069871307337^4227*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008834185099731029 20000000000000000000 10001069871307337 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001069871307337/10000000000000000 : ℝ)) (X := (20008834185099731029/20000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030898861020117819/50000000000000000000 : ℝ) ≤ (625093548121339/625000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (50030898861020117819/50000000000000000000 : ℝ)^1024 ≤ (625093548121339/625000000000000 : ℝ)^4227 := by
      have hnat : (50030898861020117819 : ℕ)^1024*625000000000000^4227 ≤ 625093548121339^4227*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030898861020117819 50000000000000000000 625093548121339 625000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625093548121339/625000000000000 : ℝ)) (X := (50030898861020117819/50000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6636032239268663/50000000000000000000 : ℝ) ≤ ((4353643285236110817/4355000000000000000 : ℝ)+2*(426898634087/261300000000000 : ℝ)*(5751/50000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (4353643285236110817/4355000000000000000 : ℝ)+2*(426898634087/261300000000000 : ℝ)*(5751/50000 : ℝ)=(40002571890693/40000000000000 : ℝ) by norm_num, show 1+2*(6636032239268663/50000000000000000000 : ℝ)=(25006636032239268663/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30898861020117819/100000000000000000000 : ℝ)+(6636032239268663/50000000000000000000 : ℝ) ≤ ((4353643285236110817/4355000000000000000 : ℝ)+(426898634087/261300000000000 : ℝ)*((2823/20000 : ℝ)+(5751/50000 : ℝ)))^(4227/1024 : ℝ) := by
    rw [show (4353643285236110817/4355000000000000000 : ℝ)+(426898634087/261300000000000 : ℝ)*((2823/20000 : ℝ)+(5751/50000 : ℝ))=(10001069871307337/10000000000000000 : ℝ) by norm_num, show 1+(30898861020117819/100000000000000000000 : ℝ)+(6636032239268663/50000000000000000000 : ℝ)=(20008834185099731029/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30898861020117819/100000000000000000000 : ℝ) ≤ ((4353643285236110817/4355000000000000000 : ℝ)+2*(426898634087/261300000000000 : ℝ)*(2823/20000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (4353643285236110817/4355000000000000000 : ℝ)+2*(426898634087/261300000000000 : ℝ)*(2823/20000 : ℝ)=(625093548121339/625000000000000 : ℝ) by norm_num, show 1+2*(30898861020117819/100000000000000000000 : ℝ)=(50030898861020117819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4353643285236110817/4355000000000000000 : ℝ)*(X 1 0+X 2 0)+(426898634087/261300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (5751/50000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (4353643285236110817/4355000000000000000 : ℝ)) (alpha := (426898634087/261300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4353643285236110817/4355000000000000000 : ℝ)*(X 0 1+X 2 1)+(426898634087/261300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (5751/50000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (4353643285236110817/4355000000000000000 : ℝ)) (alpha := (426898634087/261300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4353643285236110817/4355000000000000000 : ℝ)*(X 0 2+X 1 2)+(426898634087/261300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (5751/50000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (4353643285236110817/4355000000000000000 : ℝ)) (alpha := (426898634087/261300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-211079201/1000000000 : ℝ)*X 0 0+(539078227/1000000000 : ℝ)*X 0 1+(5267515611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534418993/1000000000 : ℝ)*X 1 0+(-434657251/2000000000 : ℝ)*X 1 1+(5267515613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344189927/10000000000 : ℝ)*X 2 0+(5267515613/10000000000 : ℝ)*X 2 1+(-2173286257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174019747/5000000000 : ℝ)*X 0 0+(4224282111/10000000000 : ℝ)*X 0 1+(447530323/1000000000 : ℝ)*X 0 2+(2174019747/5000000000 : ℝ)*X 1 0+(4224282111/10000000000 : ℝ)*X 1 1+(447530323/1000000000 : ℝ)*X 1 2+(2174019747/5000000000 : ℝ)*X 2 0+(4224282111/10000000000 : ℝ)*X 2 1+(447530323/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2110796581/10000000000 : ℝ)*X 0 0+(2633913279/5000000000 : ℝ)*X 0 1+(2695235111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212507827/400000000 : ℝ)*X 1 0+(-1025165801/5000000000 : ℝ)*X 1 1+(2695235127/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656347843/5000000000 : ℝ)*X 2 0+(5390470251/10000000000 : ℝ)*X 2 1+(-256291449/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543506109/1250000000 : ℝ)*X 0 0+(1118667529/2500000000 : ℝ)*X 0 1+(4224917521/10000000000 : ℝ)*X 0 2+(543506109/1250000000 : ℝ)*X 1 0+(1118667529/2500000000 : ℝ)*X 1 1+(4224917521/10000000000 : ℝ)*X 1 2+(543506109/1250000000 : ℝ)*X 2 0+(1118667529/2500000000 : ℝ)*X 2 1+(4224917521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1180781947169262961557083957/217750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1053478339/100000000000000 : ℝ)*(base19) + (487896817/50000000000000 : ℝ)*(base23) + (2442651/6250000000000 : ℝ)*(lower2) + (140680663/100000000000000 : ℝ)*(upper3) + (81561459/100000000000000 : ℝ)*(upper5) + (6048156101053193/100000000000000 : ℝ)*(major0) + (6048156101053193/100000000000000 : ℝ)*(major1) + (6048156101053193/100000000000000 : ℝ)*(major2) + (4056262324133779/50000000000000 : ℝ)*(sp0) + (4056276416562799/50000000000000 : ℝ)*(sp1) + (4056276455405151/50000000000000 : ℝ)*(sp2) + (1991871248527343/50000000000000 : ℝ)*(sp3) + (29238336379/100000000000000 : ℝ)*(sp4) + (7818846383/50000000000000 : ℝ)*(sp7) + (995939533686863/25000000000000 : ℝ)*(f.failure) + (253517308956373/3125000000000 : ℝ)*(f.sum) + (41615424970043/6532500000000000000000000000 : ℝ)*base65 + (10868921456267383957/1306500000000000000000000000000000 : ℝ)*base68 + (7816916172645616043/1306500000000000000000000000000000 : ℝ)*base69 + (7090920412775383957/1306500000000000000000000000000000 : ℝ)*base72 + (56563219245511/13065000000000000000000000000 : ℝ)*base73 + (16483835426508616043/1306500000000000000000000000000000 : ℝ)*base75 + (618213730233616043/1306500000000000000000000000000000 : ℝ)*base77 + (8271440747136616043/1306500000000000000000000000000000 : ℝ)*base79 + (49447781287589/13065000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5580467/625000000000000000000 : ℝ)*base90 + (5580467/625000000000000000000 : ℝ)*base92 + (5580467/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12001208373529240465803/4355000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17667877/4000000000000 : ℝ)*(base19) + (290734067/50000000000000 : ℝ)*(base23) + (32687191/20000000000000 : ℝ)*(lower1) + (66257353/100000000000000 : ℝ)*(upper3) + (24090977/50000000000000 : ℝ)*(lower4) + (2415743/12500000000000 : ℝ)*(upper5) + (3039410694114209/50000000000000 : ℝ)*(major0) + (3039410694114209/50000000000000 : ℝ)*(major1) + (3039410694114209/50000000000000 : ℝ)*(major2) + (2715603203/50000000000000 : ℝ)*(sp2) + (8153686148025129/100000000000000 : ℝ)*(sp4) + (2038421426582051/25000000000000 : ℝ)*(sp5) + (2038420033837647/25000000000000 : ℝ)*(sp6) + (2001978268286993/50000000000000 : ℝ)*(sp7) + (2001978268286993/50000000000000 : ℝ)*(f.failure) + (8153686148025129/100000000000000 : ℝ)*(f.sum) + (21894797464429/13065000000000000000000000000 : ℝ)*base66 + (35643639441319453741/653250000000000000000000000000000 : ℝ)*base68 + (3508285916076046259/653250000000000000000000000000000 : ℝ)*base69 + (71780699848604953741/653250000000000000000000000000000 : ℝ)*base72 + (35480461985777/6532500000000000000000000000 : ℝ)*base74 + (9230079686047546259/653250000000000000000000000000000 : ℝ)*base75 + (7662199051702453741/653250000000000000000000000000000 : ℝ)*base78 + (87568749007546259/653250000000000000000000000000000 : ℝ)*base79 + (2620489083527/6532500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8431363/1250000000000000000000 : ℝ)*base89 + (8431363/1250000000000000000000 : ℝ)*base91 + (8431363/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1262_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5751/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1262_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1262_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1262_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1262_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1262_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1262_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
