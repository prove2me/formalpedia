-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1504_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:53:38.00399+00:00
-- url     : https://prove2.me/submissions/afb6f971-cab6-438e-8a8a-05dfc3758f0f

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
theorem support_rectangle_w1504_s0_0 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-847175871/5000000000 : ℝ)*x 0 + (1183802919/2000000000 : ℝ)*x 1 + (970376121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847175871/5000000000 : ℝ)^4505 ≤ (10050804665823/100000000000000 : ℝ)^3481 := by
    have hnat : (847175871 : ℕ)^4505*100000000000000^3481 ≤ 10050804665823^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847175871 5000000000 10050804665823 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1183802919/2000000000 : ℝ)^4505 ≤ (3170534000607/6250000000000 : ℝ)^3481 := by
    have hnat : (1183802919 : ℕ)^4505*6250000000000^3481 ≤ 3170534000607^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183802919 2000000000 3170534000607 6250000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970376121/2000000000 : ℝ)^4505 ≤ (39220651316683/100000000000000 : ℝ)^3481 := by
    have hnat : (970376121 : ℕ)^4505*100000000000000^3481 ≤ 39220651316683^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970376121 2000000000 39220651316683 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-847175871/5000000000 : ℝ), (1183802919/2000000000 : ℝ), (970376121/2000000000 : ℝ)] ![(10050804665823/100000000000000 : ℝ), (3170534000607/6250000000000 : ℝ), (39220651316683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-847175871/5000000000 : ℝ)|^4505 ≤ (10050804665823/100000000000000 : ℝ)^3481
        have hw : |(-847175871/5000000000 : ℝ)|=(847175871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1183802919/2000000000 : ℝ)|^4505 ≤ (3170534000607/6250000000000 : ℝ)^3481
        have hw : |(1183802919/2000000000 : ℝ)|=(1183802919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(970376121/2000000000 : ℝ)|^4505 ≤ (39220651316683/100000000000000 : ℝ)^3481
        have hw : |(970376121/2000000000 : ℝ)|=(970376121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s0_1 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5479723103/10000000000 : ℝ)*x 0 + (-286640017/1250000000 : ℝ)*x 1 + (485188057/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5479723103/10000000000 : ℝ)^4505 ≤ (45910251091671/100000000000000 : ℝ)^3481 := by
    have hnat : (5479723103 : ℕ)^4505*100000000000000^3481 ≤ 45910251091671^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479723103 10000000000 45910251091671 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286640017/1250000000 : ℝ)^4505 ≤ (14869097941517/100000000000000 : ℝ)^3481 := by
    have hnat : (286640017 : ℕ)^4505*100000000000000^3481 ≤ 14869097941517^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286640017 1250000000 14869097941517 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485188057/1000000000 : ℝ)^4505 ≤ (3922065095053/10000000000000 : ℝ)^3481 := by
    have hnat : (485188057 : ℕ)^4505*10000000000000^3481 ≤ 3922065095053^3481*1000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485188057 1000000000 3922065095053 10000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5479723103/10000000000 : ℝ), (-286640017/1250000000 : ℝ), (485188057/1000000000 : ℝ)] ![(45910251091671/100000000000000 : ℝ), (14869097941517/100000000000000 : ℝ), (3922065095053/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5479723103/10000000000 : ℝ)|^4505 ≤ (45910251091671/100000000000000 : ℝ)^3481
        have hw : |(5479723103/10000000000 : ℝ)|=(5479723103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-286640017/1250000000 : ℝ)|^4505 ≤ (14869097941517/100000000000000 : ℝ)^3481
        have hw : |(-286640017/1250000000 : ℝ)|=(286640017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(485188057/1000000000 : ℝ)|^4505 ≤ (3922065095053/10000000000000 : ℝ)^3481
        have hw : |(485188057/1000000000 : ℝ)|=(485188057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s0_2 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2739861567/5000000000 : ℝ)*x 0 + (1212970143/2500000000 : ℝ)*x 1 + (-2293120093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2739861567/5000000000 : ℝ)^4505 ≤ (22955125713899/50000000000000 : ℝ)^3481 := by
    have hnat : (2739861567 : ℕ)^4505*50000000000000^3481 ≤ 22955125713899^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739861567 5000000000 22955125713899 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1212970143/2500000000 : ℝ)^4505 ≤ (39220650971453/100000000000000 : ℝ)^3481 := by
    have hnat : (1212970143 : ℕ)^4505*100000000000000^3481 ≤ 39220650971453^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212970143 2500000000 39220650971453 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2293120093/10000000000 : ℝ)^4505 ≤ (594763903227/4000000000000 : ℝ)^3481 := by
    have hnat : (2293120093 : ℕ)^4505*4000000000000^3481 ≤ 594763903227^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293120093 10000000000 594763903227 4000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2739861567/5000000000 : ℝ), (1212970143/2500000000 : ℝ), (-2293120093/10000000000 : ℝ)] ![(22955125713899/50000000000000 : ℝ), (39220650971453/100000000000000 : ℝ), (594763903227/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2739861567/5000000000 : ℝ)|^4505 ≤ (22955125713899/50000000000000 : ℝ)^3481
        have hw : |(2739861567/5000000000 : ℝ)|=(2739861567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1212970143/2500000000 : ℝ)|^4505 ≤ (39220650971453/100000000000000 : ℝ)^3481
        have hw : |(1212970143/2500000000 : ℝ)|=(1212970143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2293120093/10000000000 : ℝ)|^4505 ≤ (594763903227/4000000000000 : ℝ)^3481
        have hw : |(-2293120093/10000000000 : ℝ)|=(2293120093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s0_3 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036826969/2500000000 : ℝ)*x 0 + (3091233171/10000000000 : ℝ)*x 1 + (21989663/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036826969/2500000000 : ℝ)^4505 ≤ (2000807160349/6250000000000 : ℝ)^3481 := by
    have hnat : (1036826969 : ℕ)^4505*6250000000000^3481 ≤ 2000807160349^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036826969 2500000000 2000807160349 6250000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091233171/10000000000 : ℝ)^4505 ≤ (21884905290459/100000000000000 : ℝ)^3481 := by
    have hnat : (3091233171 : ℕ)^4505*100000000000000^3481 ≤ 21884905290459^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091233171 10000000000 21884905290459 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21989663/40000000 : ℝ)^4505 ≤ (9220436025289/20000000000000 : ℝ)^3481 := by
    have hnat : (21989663 : ℕ)^4505*20000000000000^3481 ≤ 9220436025289^3481*40000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21989663 40000000 9220436025289 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036826969/2500000000 : ℝ), (3091233171/10000000000 : ℝ), (21989663/40000000 : ℝ)] ![(2000807160349/6250000000000 : ℝ), (21884905290459/100000000000000 : ℝ), (9220436025289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036826969/2500000000 : ℝ)|^4505 ≤ (2000807160349/6250000000000 : ℝ)^3481
        have hw : |(1036826969/2500000000 : ℝ)|=(1036826969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091233171/10000000000 : ℝ)|^4505 ≤ (21884905290459/100000000000000 : ℝ)^3481
        have hw : |(3091233171/10000000000 : ℝ)|=(3091233171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21989663/40000000 : ℝ)|^4505 ≤ (9220436025289/20000000000000 : ℝ)^3481
        have hw : |(21989663/40000000 : ℝ)|=(21989663/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s0_4 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-848970463/5000000000 : ℝ)*x 0 + (195165647/400000000 : ℝ)*x 1 + (5890776497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848970463/5000000000 : ℝ)^4505 ≤ (2519591797373/25000000000000 : ℝ)^3481 := by
    have hnat : (848970463 : ℕ)^4505*25000000000000^3481 ≤ 2519591797373^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848970463 5000000000 2519591797373 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195165647/400000000 : ℝ)^4505 ≤ (19753037064471/50000000000000 : ℝ)^3481 := by
    have hnat : (195165647 : ℕ)^4505*50000000000000^3481 ≤ 19753037064471^3481*400000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195165647 400000000 19753037064471 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5890776497/10000000000 : ℝ)^4505 ≤ (12603889665789/25000000000000 : ℝ)^3481 := by
    have hnat : (5890776497 : ℕ)^4505*25000000000000^3481 ≤ 12603889665789^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5890776497 10000000000 12603889665789 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-848970463/5000000000 : ℝ), (195165647/400000000 : ℝ), (5890776497/10000000000 : ℝ)] ![(2519591797373/25000000000000 : ℝ), (19753037064471/50000000000000 : ℝ), (12603889665789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-848970463/5000000000 : ℝ)|^4505 ≤ (2519591797373/25000000000000 : ℝ)^3481
        have hw : |(-848970463/5000000000 : ℝ)|=(848970463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195165647/400000000 : ℝ)|^4505 ≤ (19753037064471/50000000000000 : ℝ)^3481
        have hw : |(195165647/400000000 : ℝ)|=(195165647/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5890776497/10000000000 : ℝ)|^4505 ≤ (12603889665789/25000000000000 : ℝ)^3481
        have hw : |(5890776497/10000000000 : ℝ)|=(5890776497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s0_5 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5188208539/10000000000 : ℝ)*x 0 + (-627112269/5000000000 : ℝ)*x 1 + (235631051/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5188208539/10000000000 : ℝ)^4505 ≤ (10693615901719/25000000000000 : ℝ)^3481 := by
    have hnat : (5188208539 : ℕ)^4505*25000000000000^3481 ≤ 10693615901719^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188208539 10000000000 10693615901719 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627112269/5000000000 : ℝ)^4505 ≤ (6809980176129/100000000000000 : ℝ)^3481 := by
    have hnat : (627112269 : ℕ)^4505*100000000000000^3481 ≤ 6809980176129^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627112269 5000000000 6809980176129 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235631051/400000000 : ℝ)^4505 ≤ (10083111240857/20000000000000 : ℝ)^3481 := by
    have hnat : (235631051 : ℕ)^4505*20000000000000^3481 ≤ 10083111240857^3481*400000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235631051 400000000 10083111240857 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5188208539/10000000000 : ℝ), (-627112269/5000000000 : ℝ), (235631051/400000000 : ℝ)] ![(10693615901719/25000000000000 : ℝ), (6809980176129/100000000000000 : ℝ), (10083111240857/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5188208539/10000000000 : ℝ)|^4505 ≤ (10693615901719/25000000000000 : ℝ)^3481
        have hw : |(5188208539/10000000000 : ℝ)|=(5188208539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-627112269/5000000000 : ℝ)|^4505 ≤ (6809980176129/100000000000000 : ℝ)^3481
        have hw : |(-627112269/5000000000 : ℝ)|=(627112269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(235631051/400000000 : ℝ)|^4505 ≤ (10083111240857/20000000000000 : ℝ)^3481
        have hw : |(235631051/400000000 : ℝ)|=(235631051/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s0_6 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1297052157/2500000000 : ℝ)*x 0 + (5890776257/10000000000 : ℝ)*x 1 + (-1254224431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1297052157/2500000000 : ℝ)^4505 ≤ (42774464556491/100000000000000 : ℝ)^3481 := by
    have hnat : (1297052157 : ℕ)^4505*100000000000000^3481 ≤ 42774464556491^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297052157 2500000000 42774464556491 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5890776257/10000000000 : ℝ)^4505 ≤ (50415556004917/100000000000000 : ℝ)^3481 := by
    have hnat : (5890776257 : ℕ)^4505*100000000000000^3481 ≤ 50415556004917^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5890776257 10000000000 50415556004917 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1254224431/10000000000 : ℝ)^4505 ≤ (1361995884851/20000000000000 : ℝ)^3481 := by
    have hnat : (1254224431 : ℕ)^4505*20000000000000^3481 ≤ 1361995884851^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254224431 10000000000 1361995884851 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1297052157/2500000000 : ℝ), (5890776257/10000000000 : ℝ), (-1254224431/10000000000 : ℝ)] ![(42774464556491/100000000000000 : ℝ), (50415556004917/100000000000000 : ℝ), (1361995884851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1297052157/2500000000 : ℝ)|^4505 ≤ (42774464556491/100000000000000 : ℝ)^3481
        have hw : |(1297052157/2500000000 : ℝ)|=(1297052157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5890776257/10000000000 : ℝ)|^4505 ≤ (50415556004917/100000000000000 : ℝ)^3481
        have hw : |(5890776257/10000000000 : ℝ)|=(5890776257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1254224431/10000000000 : ℝ)|^4505 ≤ (1361995884851/20000000000000 : ℝ)^3481
        have hw : |(-1254224431/10000000000 : ℝ)|=(1254224431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s0_7 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038850231/2500000000 : ℝ)*x 0 + (5435948437/10000000000 : ℝ)*x 1 + (3154905289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038850231/2500000000 : ℝ)^4505 ≤ (16046892185991/50000000000000 : ℝ)^3481 := by
    have hnat : (1038850231 : ℕ)^4505*50000000000000^3481 ≤ 16046892185991^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038850231 2500000000 16046892185991 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435948437/10000000000 : ℝ)^4505 ≤ (45436169472917/100000000000000 : ℝ)^3481 := by
    have hnat : (5435948437 : ℕ)^4505*100000000000000^3481 ≤ 45436169472917^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435948437 10000000000 45436169472917 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154905289/10000000000 : ℝ)^4505 ≤ (22470046139083/100000000000000 : ℝ)^3481 := by
    have hnat : (3154905289 : ℕ)^4505*100000000000000^3481 ≤ 22470046139083^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154905289 10000000000 22470046139083 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038850231/2500000000 : ℝ), (5435948437/10000000000 : ℝ), (3154905289/10000000000 : ℝ)] ![(16046892185991/50000000000000 : ℝ), (45436169472917/100000000000000 : ℝ), (22470046139083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038850231/2500000000 : ℝ)|^4505 ≤ (16046892185991/50000000000000 : ℝ)^3481
        have hw : |(1038850231/2500000000 : ℝ)|=(1038850231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435948437/10000000000 : ℝ)|^4505 ≤ (45436169472917/100000000000000 : ℝ)^3481
        have hw : |(5435948437/10000000000 : ℝ)|=(5435948437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154905289/10000000000 : ℝ)|^4505 ≤ (22470046139083/100000000000000 : ℝ)^3481
        have hw : |(3154905289/10000000000 : ℝ)|=(3154905289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1504_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (681/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6397/25000 : ℝ)*pair X 0 0 := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4503/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4503 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4503*1^1024 ≤ 0^1024*1^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4503/1024 : ℝ) ≤ (889291949376781099/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4503 ≤ (889291949376781099/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4503*50000000000000000000^1024 ≤ 889291949376781099^1024*5^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 889291949376781099 50000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (889291949376781099/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4503 := by
      have hnat : (1 : ℕ)^1024*1^4503 ≤ 1^4503*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50889291949376781099/50000000000000000000 : ℝ) ≤ (10040170698096629/10000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (50889291949376781099/50000000000000000000 : ℝ)^1024 ≤ (10040170698096629/10000000000000000 : ℝ)^4503 := by
      have hnat : (50889291949376781099 : ℕ)^1024*10000000000000000^4503 ≤ 10040170698096629^4503*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50889291949376781099 50000000000000000000 10040170698096629 10000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10040170698096629/10000000000000000 : ℝ)) (X := (50889291949376781099/50000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25889291949376781099/25000000000000000000 : ℝ) ≤ (5040170698096629/5000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (25889291949376781099/25000000000000000000 : ℝ)^1024 ≤ (5040170698096629/5000000000000000 : ℝ)^4503 := by
      have hnat : (25889291949376781099 : ℕ)^1024*5000000000000000^4503 ≤ 5040170698096629^4503*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25889291949376781099 25000000000000000000 5040170698096629 5000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5040170698096629/5000000000000000 : ℝ)) (X := (25889291949376781099/25000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(40170698096629/4000000000000000 : ℝ)*(0 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40170698096629/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(889291949376781099/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(40170698096629/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4503/1024 : ℝ) := by
    rw [show (1 : ℝ)+(40170698096629/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10040170698096629/10000000000000000 : ℝ) by norm_num, show 1+(889291949376781099/50000000000000000000 : ℝ)+(0 : ℝ)=(50889291949376781099/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(889291949376781099/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(40170698096629/4000000000000000 : ℝ)*(2/5 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40170698096629/4000000000000000 : ℝ)*(2/5 : ℝ)=(5040170698096629/5000000000000000 : ℝ) by norm_num, show 1+2*(889291949376781099/50000000000000000000 : ℝ)=(25889291949376781099/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(40170698096629/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40170698096629/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(40170698096629/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40170698096629/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(40170698096629/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40170698096629/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-847175871/5000000000 : ℝ)*X 0 0+(1183802919/2000000000 : ℝ)*X 0 1+(970376121/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5479723103/10000000000 : ℝ)*X 1 0+(-286640017/1250000000 : ℝ)*X 1 1+(485188057/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2739861567/5000000000 : ℝ)*X 2 0+(1212970143/2500000000 : ℝ)*X 2 1+(-2293120093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1036826969/2500000000 : ℝ)*X 0 0+(3091233171/10000000000 : ℝ)*X 0 1+(21989663/40000000 : ℝ)*X 0 2+(1036826969/2500000000 : ℝ)*X 1 0+(3091233171/10000000000 : ℝ)*X 1 1+(21989663/40000000 : ℝ)*X 1 2+(1036826969/2500000000 : ℝ)*X 2 0+(3091233171/10000000000 : ℝ)*X 2 1+(21989663/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-848970463/5000000000 : ℝ)*X 0 0+(195165647/400000000 : ℝ)*X 0 1+(5890776497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5188208539/10000000000 : ℝ)*X 1 0+(-627112269/5000000000 : ℝ)*X 1 1+(235631051/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1297052157/2500000000 : ℝ)*X 2 0+(5890776257/10000000000 : ℝ)*X 2 1+(-1254224431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1038850231/2500000000 : ℝ)*X 0 0+(5435948437/10000000000 : ℝ)*X 0 1+(3154905289/10000000000 : ℝ)*X 0 2+(1038850231/2500000000 : ℝ)*X 1 0+(5435948437/10000000000 : ℝ)*X 1 1+(3154905289/10000000000 : ℝ)*X 1 2+(1038850231/2500000000 : ℝ)*X 2 0+(5435948437/10000000000 : ℝ)*X 2 1+(3154905289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3557560874223156501/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30971917/100000000000000 : ℝ)*(base1) + (81047693/10000000000000 : ℝ)*(base19) + (407889139/50000000000000 : ℝ)*(base23) + (96829737/100000000000000 : ℝ)*(upper3) + (11043271/10000000000000 : ℝ)*(upper5) + (676346845776421/100000000000000 : ℝ)*(major0) + (676346845776421/100000000000000 : ℝ)*(major1) + (676346845776421/100000000000000 : ℝ)*(major2) + (468546051526371/50000000000000 : ℝ)*(sp0) + (187418833912123/20000000000000 : ℝ)*(sp1) + (937094164259267/100000000000000 : ℝ)*(sp2) + (415597295523853/100000000000000 : ℝ)*(sp3) + (1453978359/50000000000000 : ℝ)*(sp4) + (1266434157/100000000000000 : ℝ)*(sp7) + (207799296464963/50000000000000 : ℝ)*(f.failure) + (117136872504693/12500000000000 : ℝ)*(f.sum) + (461389585015191/200000000000000000000000000000 : ℝ)*base66 + (2147942942984809/400000000000000000000000000000 : ℝ)*base67 + (2718085636184809/400000000000000000000000000000 : ℝ)*base69 + (1157173868615191/400000000000000000000000000000 : ℝ)*base72 + (704103021384809/200000000000000000000000000000 : ℝ)*base73 + (3068404281415191/400000000000000000000000000000 : ℝ)*base76 + (1148931641815191/400000000000000000000000000000 : ℝ)*base78 + (2837588090615191/400000000000000000000000000000 : ℝ)*base80 + (612214529384809/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1709387/625000000000000000000 : ℝ)*base90 + (1709387/625000000000000000000 : ℝ)*base92 + (1709387/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107146752546379499839161/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (105175763/10000000000000 : ℝ)*(base19) + (1082768259/100000000000000 : ℝ)*(base23) + (81299423/100000000000000 : ℝ)*(base32) + (151453361/100000000000000 : ℝ)*(upper3) + (53610311/50000000000000 : ℝ)*(upper5) + (71344708781497/10000000000000 : ℝ)*(major0) + (71344708781497/10000000000000 : ℝ)*(major1) + (71344708781497/10000000000000 : ℝ)*(major2) + (2491036569/100000000000000 : ℝ)*(sp1) + (1370578117/50000000000000 : ℝ)*(sp2) + (988498212880839/100000000000000 : ℝ)*(sp4) + (12356183376083/1250000000000 : ℝ)*(sp5) + (494247194478173/50000000000000 : ℝ)*(sp6) + (54799462858969/12500000000000 : ℝ)*(sp7) + (54799473021397/12500000000000 : ℝ)*(f.failure) + (988498212880839/100000000000000 : ℝ)*(f.sum) + (15540114593613/20000000000000000000000000000 : ℝ)*base65 + (153332144686387/40000000000000000000000000000 : ℝ)*base68 + (75186260833613/40000000000000000000000000000 : ℝ)*base69 + (120131103326387/40000000000000000000000000000 : ℝ)*base72 + (14872765126387/20000000000000000000000000000 : ℝ)*base74 + (61018686953613/40000000000000000000000000000 : ℝ)*base75 + (140359026406387/40000000000000000000000000000 : ℝ)*base78 + (20503177513613/40000000000000000000000000000 : ℝ)*base79 + (54035804473613/20000000000000000000000000000 : ℝ)*base81 + (1938747/156250000000000000000 : ℝ)*base89 + (1938747/156250000000000000000 : ℝ)*base91 + (1938747/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1504_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (681/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6397/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1504_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1504_s1_0 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-462554059/2500000000 : ℝ)*x 0 + (5575886509/10000000000 : ℝ)*x 1 + (636858337/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (462554059/2500000000 : ℝ)^4505 ≤ (11263219335529/100000000000000 : ℝ)^3481 := by
    have hnat : (462554059 : ℕ)^4505*100000000000000^3481 ≤ 11263219335529^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462554059 2500000000 11263219335529 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5575886509/10000000000 : ℝ)^4505 ≤ (11738903223183/25000000000000 : ℝ)^3481 := by
    have hnat : (5575886509 : ℕ)^4505*25000000000000^3481 ≤ 11738903223183^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5575886509 10000000000 11738903223183 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (636858337/1250000000 : ℝ)^4505 ≤ (20890583882807/50000000000000 : ℝ)^3481 := by
    have hnat : (636858337 : ℕ)^4505*50000000000000^3481 ≤ 20890583882807^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636858337 1250000000 20890583882807 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-462554059/2500000000 : ℝ), (5575886509/10000000000 : ℝ), (636858337/1250000000 : ℝ)] ![(11263219335529/100000000000000 : ℝ), (11738903223183/25000000000000 : ℝ), (20890583882807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-462554059/2500000000 : ℝ)|^4505 ≤ (11263219335529/100000000000000 : ℝ)^3481
        have hw : |(-462554059/2500000000 : ℝ)|=(462554059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5575886509/10000000000 : ℝ)|^4505 ≤ (11738903223183/25000000000000 : ℝ)^3481
        have hw : |(5575886509/10000000000 : ℝ)|=(5575886509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(636858337/1250000000 : ℝ)|^4505 ≤ (20890583882807/50000000000000 : ℝ)^3481
        have hw : |(636858337/1250000000 : ℝ)|=(636858337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s1_1 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388085619/10000000000 : ℝ)*x 0 + (-2103759013/10000000000 : ℝ)*x 1 + (254743357/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388085619/10000000000 : ℝ)^4505 ≤ (8983819393027/20000000000000 : ℝ)^3481 := by
    have hnat : (5388085619 : ℕ)^4505*20000000000000^3481 ≤ 8983819393027^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388085619 10000000000 8983819393027 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2103759013/10000000000 : ℝ)^4505 ≤ (13299730541401/100000000000000 : ℝ)^3481 := by
    have hnat : (2103759013 : ℕ)^4505*100000000000000^3481 ≤ 13299730541401^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103759013 10000000000 13299730541401 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254743357/500000000 : ℝ)^4505 ≤ (4178117247779/10000000000000 : ℝ)^3481 := by
    have hnat : (254743357 : ℕ)^4505*10000000000000^3481 ≤ 4178117247779^3481*500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254743357 500000000 4178117247779 10000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388085619/10000000000 : ℝ), (-2103759013/10000000000 : ℝ), (254743357/500000000 : ℝ)] ![(8983819393027/20000000000000 : ℝ), (13299730541401/100000000000000 : ℝ), (4178117247779/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388085619/10000000000 : ℝ)|^4505 ≤ (8983819393027/20000000000000 : ℝ)^3481
        have hw : |(5388085619/10000000000 : ℝ)|=(5388085619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2103759013/10000000000 : ℝ)|^4505 ≤ (13299730541401/100000000000000 : ℝ)^3481
        have hw : |(-2103759013/10000000000 : ℝ)|=(2103759013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(254743357/500000000 : ℝ)|^4505 ≤ (4178117247779/10000000000000 : ℝ)^3481
        have hw : |(254743357/500000000 : ℝ)|=(254743357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s1_2 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388085987/10000000000 : ℝ)*x 0 + (1273716731/2500000000 : ℝ)*x 1 + (-262969851/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388085987/10000000000 : ℝ)^4505 ≤ (44919100935543/100000000000000 : ℝ)^3481 := by
    have hnat : (5388085987 : ℕ)^4505*100000000000000^3481 ≤ 44919100935543^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388085987 10000000000 44919100935543 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1273716731/2500000000 : ℝ)^4505 ≤ (2089058509269/5000000000000 : ℝ)^3481 := by
    have hnat : (1273716731 : ℕ)^4505*5000000000000^3481 ≤ 2089058509269^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273716731 2500000000 2089058509269 5000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262969851/1250000000 : ℝ)^4505 ≤ (531989154567/4000000000000 : ℝ)^3481 := by
    have hnat : (262969851 : ℕ)^4505*4000000000000^3481 ≤ 531989154567^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262969851 1250000000 531989154567 4000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388085987/10000000000 : ℝ), (1273716731/2500000000 : ℝ), (-262969851/1250000000 : ℝ)] ![(44919100935543/100000000000000 : ℝ), (2089058509269/5000000000000 : ℝ), (531989154567/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388085987/10000000000 : ℝ)|^4505 ≤ (44919100935543/100000000000000 : ℝ)^3481
        have hw : |(5388085987/10000000000 : ℝ)|=(5388085987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1273716731/2500000000 : ℝ)|^4505 ≤ (2089058509269/5000000000000 : ℝ)^3481
        have hw : |(1273716731/2500000000 : ℝ)|=(1273716731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262969851/1250000000 : ℝ)|^4505 ≤ (531989154567/4000000000000 : ℝ)^3481
        have hw : |(-262969851/1250000000 : ℝ)|=(262969851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s1_3 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2126265101/5000000000 : ℝ)*x 0 + (934903669/2500000000 : ℝ)*x 1 + (4824221439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126265101/5000000000 : ℝ)^4505 ≤ (8266986692843/25000000000000 : ℝ)^3481 := by
    have hnat : (2126265101 : ℕ)^4505*25000000000000^3481 ≤ 8266986692843^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126265101 5000000000 8266986692843 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (934903669/2500000000 : ℝ)^4505 ≤ (1120020652739/4000000000000 : ℝ)^3481 := by
    have hnat : (934903669 : ℕ)^4505*4000000000000^3481 ≤ 1120020652739^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934903669 2500000000 1120020652739 4000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4824221439/10000000000 : ℝ)^4505 ≤ (38931536894039/100000000000000 : ℝ)^3481 := by
    have hnat : (4824221439 : ℕ)^4505*100000000000000^3481 ≤ 38931536894039^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824221439 10000000000 38931536894039 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126265101/5000000000 : ℝ), (934903669/2500000000 : ℝ), (4824221439/10000000000 : ℝ)] ![(8266986692843/25000000000000 : ℝ), (1120020652739/4000000000000 : ℝ), (38931536894039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126265101/5000000000 : ℝ)|^4505 ≤ (8266986692843/25000000000000 : ℝ)^3481
        have hw : |(2126265101/5000000000 : ℝ)|=(2126265101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(934903669/2500000000 : ℝ)|^4505 ≤ (1120020652739/4000000000000 : ℝ)^3481
        have hw : |(934903669/2500000000 : ℝ)|=(934903669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4824221439/10000000000 : ℝ)|^4505 ≤ (38931536894039/100000000000000 : ℝ)^3481
        have hw : |(4824221439/10000000000 : ℝ)|=(4824221439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s1_4 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-925266723/5000000000 : ℝ)*x 0 + (1275076853/2500000000 : ℝ)*x 1 + (696294667/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925266723/5000000000 : ℝ)^4505 ≤ (11265718464371/100000000000000 : ℝ)^3481 := by
    have hnat : (925266723 : ℕ)^4505*100000000000000^3481 ≤ 11265718464371^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925266723 5000000000 11265718464371 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1275076853/2500000000 : ℝ)^4505 ≤ (20919459599577/50000000000000 : ℝ)^3481 := by
    have hnat : (1275076853 : ℕ)^4505*50000000000000^3481 ≤ 20919459599577^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275076853 2500000000 20919459599577 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (696294667/1250000000 : ℝ)^4505 ≤ (5861920290053/12500000000000 : ℝ)^3481 := by
    have hnat : (696294667 : ℕ)^4505*12500000000000^3481 ≤ 5861920290053^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696294667 1250000000 5861920290053 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-925266723/5000000000 : ℝ), (1275076853/2500000000 : ℝ), (696294667/1250000000 : ℝ)] ![(11265718464371/100000000000000 : ℝ), (20919459599577/50000000000000 : ℝ), (5861920290053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-925266723/5000000000 : ℝ)|^4505 ≤ (11265718464371/100000000000000 : ℝ)^3481
        have hw : |(-925266723/5000000000 : ℝ)|=(925266723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1275076853/2500000000 : ℝ)|^4505 ≤ (20919459599577/50000000000000 : ℝ)^3481
        have hw : |(1275076853/2500000000 : ℝ)|=(1275076853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(696294667/1250000000 : ℝ)|^4505 ≤ (5861920290053/12500000000000 : ℝ)^3481
        have hw : |(696294667/1250000000 : ℝ)|=(696294667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s1_5 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630755607/5000000000 : ℝ)*x 0 + (-814134217/5000000000 : ℝ)*x 1 + (2785178741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630755607/5000000000 : ℝ)^4505 ≤ (8711642284117/20000000000000 : ℝ)^3481 := by
    have hnat : (2630755607 : ℕ)^4505*20000000000000^3481 ≤ 8711642284117^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630755607 5000000000 8711642284117 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (814134217/5000000000 : ℝ)^4505 ≤ (9546424643591/100000000000000 : ℝ)^3481 := by
    have hnat : (814134217 : ℕ)^4505*100000000000000^3481 ≤ 9546424643591^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814134217 5000000000 9546424643591 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2785178741/5000000000 : ℝ)^4505 ≤ (11723840977783/25000000000000 : ℝ)^3481 := by
    have hnat : (2785178741 : ℕ)^4505*25000000000000^3481 ≤ 11723840977783^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785178741 5000000000 11723840977783 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630755607/5000000000 : ℝ), (-814134217/5000000000 : ℝ), (2785178741/5000000000 : ℝ)] ![(8711642284117/20000000000000 : ℝ), (9546424643591/100000000000000 : ℝ), (11723840977783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630755607/5000000000 : ℝ)|^4505 ≤ (8711642284117/20000000000000 : ℝ)^3481
        have hw : |(2630755607/5000000000 : ℝ)|=(2630755607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-814134217/5000000000 : ℝ)|^4505 ≤ (9546424643591/100000000000000 : ℝ)^3481
        have hw : |(-814134217/5000000000 : ℝ)|=(814134217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2785178741/5000000000 : ℝ)|^4505 ≤ (11723840977783/25000000000000 : ℝ)^3481
        have hw : |(2785178741/5000000000 : ℝ)|=(2785178741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s1_6 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052302213/2000000000 : ℝ)*x 0 + (1392589383/2500000000 : ℝ)*x 1 + (-814134287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052302213/2000000000 : ℝ)^4505 ≤ (10889552456051/25000000000000 : ℝ)^3481 := by
    have hnat : (1052302213 : ℕ)^4505*25000000000000^3481 ≤ 10889552456051^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052302213 2000000000 10889552456051 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1392589383/2500000000 : ℝ)^4505 ≤ (9379072891179/20000000000000 : ℝ)^3481 := by
    have hnat : (1392589383 : ℕ)^4505*20000000000000^3481 ≤ 9379072891179^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392589383 2500000000 9379072891179 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (814134287/5000000000 : ℝ)^4505 ≤ (9546425705857/100000000000000 : ℝ)^3481 := by
    have hnat : (814134287 : ℕ)^4505*100000000000000^3481 ≤ 9546425705857^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814134287 5000000000 9546425705857 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052302213/2000000000 : ℝ), (1392589383/2500000000 : ℝ), (-814134287/5000000000 : ℝ)] ![(10889552456051/25000000000000 : ℝ), (9379072891179/20000000000000 : ℝ), (9546425705857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052302213/2000000000 : ℝ)|^4505 ≤ (10889552456051/25000000000000 : ℝ)^3481
        have hw : |(1052302213/2000000000 : ℝ)|=(1052302213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1392589383/2500000000 : ℝ)|^4505 ≤ (9379072891179/20000000000000 : ℝ)^3481
        have hw : |(1392589383/2500000000 : ℝ)|=(1392589383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-814134287/5000000000 : ℝ)|^4505 ≤ (9546425705857/100000000000000 : ℝ)^3481
        have hw : |(-814134287/5000000000 : ℝ)|=(814134287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s1_7 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33228483/78125000 : ℝ)*x 0 + (4811954853/10000000000 : ℝ)*x 1 + (3752081239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33228483/78125000 : ℝ)^4505 ≤ (33075148637223/100000000000000 : ℝ)^3481 := by
    have hnat : (33228483 : ℕ)^4505*100000000000000^3481 ≤ 33075148637223^3481*78125000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33228483 78125000 33075148637223 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4811954853/10000000000 : ℝ)^4505 ≤ (38803473135461/100000000000000 : ℝ)^3481 := by
    have hnat : (4811954853 : ℕ)^4505*100000000000000^3481 ≤ 38803473135461^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4811954853 10000000000 38803473135461 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3752081239/10000000000 : ℝ)^4505 ≤ (1757586138697/6250000000000 : ℝ)^3481 := by
    have hnat : (3752081239 : ℕ)^4505*6250000000000^3481 ≤ 1757586138697^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3752081239 10000000000 1757586138697 6250000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33228483/78125000 : ℝ), (4811954853/10000000000 : ℝ), (3752081239/10000000000 : ℝ)] ![(33075148637223/100000000000000 : ℝ), (38803473135461/100000000000000 : ℝ), (1757586138697/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33228483/78125000 : ℝ)|^4505 ≤ (33075148637223/100000000000000 : ℝ)^3481
        have hw : |(33228483/78125000 : ℝ)|=(33228483/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4811954853/10000000000 : ℝ)|^4505 ≤ (38803473135461/100000000000000 : ℝ)^3481
        have hw : |(4811954853/10000000000 : ℝ)|=(4811954853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3752081239/10000000000 : ℝ)|^4505 ≤ (1757586138697/6250000000000 : ℝ)^3481
        have hw : |(3752081239/10000000000 : ℝ)|=(3752081239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1504_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6397/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1031/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (921/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6397/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (681/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6397/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (681/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6397/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (681/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6397/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (681/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6397/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (681/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6397/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (681/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (681/25000 : ℝ) ^ (4503/1024 : ℝ) ≤ (6574373381827/50000000000000000000 : ℝ) := by
    have hpowers : (681/25000 : ℝ)^4503 ≤ (6574373381827/50000000000000000000 : ℝ)^1024 := by
      have hnat : (681 : ℕ)^4503*50000000000000000000^1024 ≤ 6574373381827^1024*25000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        681 25000 6574373381827 50000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (681/25000 : ℝ)) (X := (6574373381827/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6397/25000 : ℝ) ^ (4503/1024 : ℝ) ≤ (249380756317920073/100000000000000000000 : ℝ) := by
    have hpowers : (6397/25000 : ℝ)^4503 ≤ (249380756317920073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6397 : ℕ)^4503*100000000000000000000^1024 ≤ 249380756317920073^1024*25000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6397 25000 249380756317920073 100000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6397/25000 : ℝ)) (X := (249380756317920073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000006574373381827/25000000000000000000 : ℝ) ≤ (5000000299007669/5000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (25000006574373381827/25000000000000000000 : ℝ)^1024 ≤ (5000000299007669/5000000000000000 : ℝ)^4503 := by
      have hnat : (25000006574373381827 : ℕ)^1024*5000000000000000^4503 ≤ 5000000299007669^4503*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000006574373381827 25000000000000000000 5000000299007669 5000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000299007669/5000000000000000 : ℝ)) (X := (25000006574373381827/25000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100249393905064683727/100000000000000000000 : ℝ) ≤ (500283293012753/500000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (100249393905064683727/100000000000000000000 : ℝ)^1024 ≤ (500283293012753/500000000000000 : ℝ)^4503 := by
      have hnat : (100249393905064683727 : ℕ)^1024*500000000000000^4503 ≤ 500283293012753^4503*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100249393905064683727 100000000000000000000 500283293012753 500000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500283293012753/500000000000000 : ℝ)) (X := (100249393905064683727/100000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50249380756317920073/50000000000000000000 : ℝ) ≤ (5005665561247391/5000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (50249380756317920073/50000000000000000000 : ℝ)^1024 ≤ (5005665561247391/5000000000000000 : ℝ)^4503 := by
      have hnat : (50249380756317920073 : ℕ)^1024*5000000000000000^4503 ≤ 5005665561247391^4503*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50249380756317920073 50000000000000000000 5005665561247391 5000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005665561247391/5000000000000000 : ℝ)) (X := (50249380756317920073/50000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6574373381827/50000000000000000000 : ℝ) ≤ ((14288071832771292661/14290000000000000000 : ℝ)+2*(2832631119861/1143200000000000 : ℝ)*(681/25000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (14288071832771292661/14290000000000000000 : ℝ)+2*(2832631119861/1143200000000000 : ℝ)*(681/25000 : ℝ)=(5000000299007669/5000000000000000 : ℝ) by norm_num, show 1+2*(6574373381827/50000000000000000000 : ℝ)=(25000006574373381827/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(249380756317920073/100000000000000000000 : ℝ)+(6574373381827/50000000000000000000 : ℝ) ≤ ((14288071832771292661/14290000000000000000 : ℝ)+(2832631119861/1143200000000000 : ℝ)*((6397/25000 : ℝ)+(681/25000 : ℝ)))^(4503/1024 : ℝ) := by
    rw [show (14288071832771292661/14290000000000000000 : ℝ)+(2832631119861/1143200000000000 : ℝ)*((6397/25000 : ℝ)+(681/25000 : ℝ))=(500283293012753/500000000000000 : ℝ) by norm_num, show 1+(249380756317920073/100000000000000000000 : ℝ)+(6574373381827/50000000000000000000 : ℝ)=(100249393905064683727/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(249380756317920073/100000000000000000000 : ℝ) ≤ ((14288071832771292661/14290000000000000000 : ℝ)+2*(2832631119861/1143200000000000 : ℝ)*(6397/25000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (14288071832771292661/14290000000000000000 : ℝ)+2*(2832631119861/1143200000000000 : ℝ)*(6397/25000 : ℝ)=(5005665561247391/5000000000000000 : ℝ) by norm_num, show 1+2*(249380756317920073/100000000000000000000 : ℝ)=(50249380756317920073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14288071832771292661/14290000000000000000 : ℝ)*(X 1 0+X 2 0)+(2832631119861/1143200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (681/25000 : ℝ)) (hi := (6397/25000 : ℝ)) (c := (14288071832771292661/14290000000000000000 : ℝ)) (alpha := (2832631119861/1143200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14288071832771292661/14290000000000000000 : ℝ)*(X 0 1+X 2 1)+(2832631119861/1143200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (681/25000 : ℝ)) (hi := (6397/25000 : ℝ)) (c := (14288071832771292661/14290000000000000000 : ℝ)) (alpha := (2832631119861/1143200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14288071832771292661/14290000000000000000 : ℝ)*(X 0 2+X 1 2)+(2832631119861/1143200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (681/25000 : ℝ)) (hi := (6397/25000 : ℝ)) (c := (14288071832771292661/14290000000000000000 : ℝ)) (alpha := (2832631119861/1143200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-462554059/2500000000 : ℝ)*X 0 0+(5575886509/10000000000 : ℝ)*X 0 1+(636858337/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5388085619/10000000000 : ℝ)*X 1 0+(-2103759013/10000000000 : ℝ)*X 1 1+(254743357/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5388085987/10000000000 : ℝ)*X 2 0+(1273716731/2500000000 : ℝ)*X 2 1+(-262969851/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2126265101/5000000000 : ℝ)*X 0 0+(934903669/2500000000 : ℝ)*X 0 1+(4824221439/10000000000 : ℝ)*X 0 2+(2126265101/5000000000 : ℝ)*X 1 0+(934903669/2500000000 : ℝ)*X 1 1+(4824221439/10000000000 : ℝ)*X 1 2+(2126265101/5000000000 : ℝ)*X 2 0+(934903669/2500000000 : ℝ)*X 2 1+(4824221439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-925266723/5000000000 : ℝ)*X 0 0+(1275076853/2500000000 : ℝ)*X 0 1+(696294667/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2630755607/5000000000 : ℝ)*X 1 0+(-814134217/5000000000 : ℝ)*X 1 1+(2785178741/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1052302213/2000000000 : ℝ)*X 2 0+(1392589383/2500000000 : ℝ)*X 2 1+(-814134287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33228483/78125000 : ℝ)*X 0 0+(4811954853/10000000000 : ℝ)*X 0 1+(3752081239/10000000000 : ℝ)*X 0 2+(33228483/78125000 : ℝ)*X 1 0+(4811954853/10000000000 : ℝ)*X 1 1+(3752081239/10000000000 : ℝ)*X 1 2+(33228483/78125000 : ℝ)*X 2 0+(4811954853/10000000000 : ℝ)*X 2 1+(3752081239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (257420801535525790115388753/178625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60455381/12500000000000 : ℝ)*(base19) + (115037273/20000000000000 : ℝ)*(base23) + (8880299/100000000000000 : ℝ)*(upper3) + (27180201/100000000000000 : ℝ)*(upper4) + (50689257/50000000000000 : ℝ)*(upper5) + (375115698731809/25000000000000 : ℝ)*(major0) + (375115698731809/25000000000000 : ℝ)*(major1) + (375115698731809/25000000000000 : ℝ)*(major2) + (41578422254529/2000000000000 : ℝ)*(sp0) + (2078927372800543/100000000000000 : ℝ)*(sp1) + (1039463640628613/50000000000000 : ℝ)*(sp2) + (460997765780283/50000000000000 : ℝ)*(sp3) + (6743717141/100000000000000 : ℝ)*(sp4) + (2153812839/100000000000000 : ℝ)*(sp7) + (184399537074681/20000000000000 : ℝ)*(f.failure) + (2078927856443591/100000000000000 : ℝ)*(f.sum) + (12561211278231/14290000000000000000000000000 : ℝ)*base66 + (862282739060433751/357250000000000000000000000000000 : ℝ)*base68 + (1952214519031066249/357250000000000000000000000000000 : ℝ)*base69 + (1094017060579566249/357250000000000000000000000000000 : ℝ)*base71 + (55828068042411/14290000000000000000000000000 : ℝ)*base74 + (249607059337933751/357250000000000000000000000000000 : ℝ)*base76 + (1215696072978316249/357250000000000000000000000000000 : ℝ)*base77 + (406961962295066249/357250000000000000000000000000000 : ℝ)*base79 + (42007342878319/14290000000000000000000000000 : ℝ)*base81 + (948769/250000000000000000000 : ℝ)*base90 + (948769/250000000000000000000 : ℝ)*base92 + (948769/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1208831078890173642684020913/357250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169647649/25000000000000 : ℝ)*(base19) + (166505619/25000000000000 : ℝ)*(base23) + (111051321/100000000000000 : ℝ)*(upper3) + (19339613/100000000000000 : ℝ)*(lower4) + (204543/1250000000000 : ℝ)*(upper5) + (1535470578906961/100000000000000 : ℝ)*(major0) + (1535470578906961/100000000000000 : ℝ)*(major1) + (1535470578906961/100000000000000 : ℝ)*(major2) + (4639433057/100000000000000 : ℝ)*(sp1) + (2546702357/50000000000000 : ℝ)*(sp2) + (66482247896981/3125000000000 : ℝ)*(sp4) + (2127426614679739/100000000000000 : ℝ)*(sp5) + (1063713086638101/50000000000000 : ℝ)*(sp6) + (235877278080033/25000000000000 : ℝ)*(sp7) + (235877278080033/25000000000000 : ℝ)*(f.failure) + (66482247896981/3125000000000 : ℝ)*(f.sum) + (37327565110661/57160000000000000000000000000 : ℝ)*base65 + (188807529676375721/1429000000000000000000000000000000 : ℝ)*base67 + (3784305703963624279/1429000000000000000000000000000000 : ℝ)*base70 + (346763231936624279/1429000000000000000000000000000000 : ℝ)*base72 + (81197649961219/57160000000000000000000000000 : ℝ)*base74 + (315008749877624279/1429000000000000000000000000000000 : ℝ)*base76 + (2126321823687624279/1429000000000000000000000000000000 : ℝ)*base78 + (1834930403907624279/1429000000000000000000000000000000 : ℝ)*base80 + (112879012033659/57160000000000000000000000000 : ℝ)*base82 + (259183/312500000000000000000 : ℝ)*base89 + (259183/312500000000000000000 : ℝ)*base91 + (259183/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1504_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6397/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1031/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (921/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1504_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1504_s2_0 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-937834627/5000000000 : ℝ)*x 0 + (5460519883/10000000000 : ℝ)*x 1 + (1298440063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (937834627/5000000000 : ℝ)^4505 ≤ (2292829901333/20000000000000 : ℝ)^3481 := by
    have hnat : (937834627 : ℕ)^4505*20000000000000^3481 ≤ 2292829901333^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937834627 5000000000 2292829901333 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460519883/10000000000 : ℝ)^4505 ≤ (45702141648719/100000000000000 : ℝ)^3481 := by
    have hnat : (5460519883 : ℕ)^4505*100000000000000^3481 ≤ 45702141648719^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460519883 10000000000 45702141648719 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298440063/2500000000 : ℝ)^4505 ≤ (42833708818851/100000000000000 : ℝ)^3481 := by
    have hnat : (1298440063 : ℕ)^4505*100000000000000^3481 ≤ 42833708818851^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298440063 2500000000 42833708818851 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-937834627/5000000000 : ℝ), (5460519883/10000000000 : ℝ), (1298440063/2500000000 : ℝ)] ![(2292829901333/20000000000000 : ℝ), (45702141648719/100000000000000 : ℝ), (42833708818851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-937834627/5000000000 : ℝ)|^4505 ≤ (2292829901333/20000000000000 : ℝ)^3481
        have hw : |(-937834627/5000000000 : ℝ)|=(937834627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460519883/10000000000 : ℝ)|^4505 ≤ (45702141648719/100000000000000 : ℝ)^3481
        have hw : |(5460519883/10000000000 : ℝ)|=(5460519883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298440063/2500000000 : ℝ)|^4505 ≤ (42833708818851/100000000000000 : ℝ)^3481
        have hw : |(1298440063/2500000000 : ℝ)|=(1298440063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s2_1 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358845661/10000000000 : ℝ)*x 0 + (-1006529/5000000 : ℝ)*x 1 + (519376117/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358845661/10000000000 : ℝ)^4505 ≤ (8920774950721/20000000000000 : ℝ)^3481 := by
    have hnat : (5358845661 : ℕ)^4505*20000000000000^3481 ≤ 8920774950721^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358845661 10000000000 8920774950721 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006529/5000000 : ℝ)^4505 ≤ (6281203302687/50000000000000 : ℝ)^3481 := by
    have hnat : (1006529 : ℕ)^4505*50000000000000^3481 ≤ 6281203302687^3481*5000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006529 5000000 6281203302687 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519376117/1000000000 : ℝ)^4505 ≤ (42833718616847/100000000000000 : ℝ)^3481 := by
    have hnat : (519376117 : ℕ)^4505*100000000000000^3481 ≤ 42833718616847^3481*1000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519376117 1000000000 42833718616847 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358845661/10000000000 : ℝ), (-1006529/5000000 : ℝ), (519376117/1000000000 : ℝ)] ![(8920774950721/20000000000000 : ℝ), (6281203302687/50000000000000 : ℝ), (42833718616847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358845661/10000000000 : ℝ)|^4505 ≤ (8920774950721/20000000000000 : ℝ)^3481
        have hw : |(5358845661/10000000000 : ℝ)|=(5358845661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1006529/5000000 : ℝ)|^4505 ≤ (6281203302687/50000000000000 : ℝ)^3481
        have hw : |(-1006529/5000000 : ℝ)|=(1006529/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519376117/1000000000 : ℝ)|^4505 ≤ (42833718616847/100000000000000 : ℝ)^3481
        have hw : |(519376117/1000000000 : ℝ)|=(519376117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s2_2 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679423299/5000000000 : ℝ)*x 0 + (2596880267/5000000000 : ℝ)*x 1 + (-251632199/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679423299/5000000000 : ℝ)^4505 ≤ (44603884846871/100000000000000 : ℝ)^3481 := by
    have hnat : (2679423299 : ℕ)^4505*100000000000000^3481 ≤ 44603884846871^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679423299 5000000000 44603884846871 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596880267/5000000000 : ℝ)^4505 ≤ (42833711828693/100000000000000 : ℝ)^3481 := by
    have hnat : (2596880267 : ℕ)^4505*100000000000000^3481 ≤ 42833711828693^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596880267 5000000000 42833711828693 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251632199/1250000000 : ℝ)^4505 ≤ (6281201655141/50000000000000 : ℝ)^3481 := by
    have hnat : (251632199 : ℕ)^4505*50000000000000^3481 ≤ 6281201655141^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251632199 1250000000 6281201655141 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679423299/5000000000 : ℝ), (2596880267/5000000000 : ℝ), (-251632199/1250000000 : ℝ)] ![(44603884846871/100000000000000 : ℝ), (42833711828693/100000000000000 : ℝ), (6281201655141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679423299/5000000000 : ℝ)|^4505 ≤ (44603884846871/100000000000000 : ℝ)^3481
        have hw : |(2679423299/5000000000 : ℝ)|=(2679423299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596880267/5000000000 : ℝ)|^4505 ≤ (42833711828693/100000000000000 : ℝ)^3481
        have hw : |(2596880267/5000000000 : ℝ)|=(2596880267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251632199/1250000000 : ℝ)|^4505 ≤ (6281201655141/50000000000000 : ℝ)^3481
        have hw : |(-251632199/1250000000 : ℝ)|=(251632199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s2_3 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170831019/400000000 : ℝ)*x 0 + (3979070667/10000000000 : ℝ)*x 1 + (1145140797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170831019/400000000 : ℝ)^4505 ≤ (33251674482041/100000000000000 : ℝ)^3481 := by
    have hnat : (170831019 : ℕ)^4505*100000000000000^3481 ≤ 33251674482041^3481*400000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170831019 400000000 33251674482041 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979070667/10000000000 : ℝ)^4505 ≤ (6068482163631/20000000000000 : ℝ)^3481 := by
    have hnat : (3979070667 : ℕ)^4505*20000000000000^3481 ≤ 6068482163631^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979070667 10000000000 6068482163631 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145140797/2500000000 : ℝ)^4505 ≤ (7281182938087/20000000000000 : ℝ)^3481 := by
    have hnat : (1145140797 : ℕ)^4505*20000000000000^3481 ≤ 7281182938087^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145140797 2500000000 7281182938087 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170831019/400000000 : ℝ), (3979070667/10000000000 : ℝ), (1145140797/2500000000 : ℝ)] ![(33251674482041/100000000000000 : ℝ), (6068482163631/20000000000000 : ℝ), (7281182938087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170831019/400000000 : ℝ)|^4505 ≤ (33251674482041/100000000000000 : ℝ)^3481
        have hw : |(170831019/400000000 : ℝ)|=(170831019/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979070667/10000000000 : ℝ)|^4505 ≤ (6068482163631/20000000000000 : ℝ)^3481
        have hw : |(3979070667/10000000000 : ℝ)|=(3979070667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1145140797/2500000000 : ℝ)|^4505 ≤ (7281182938087/20000000000000 : ℝ)^3481
        have hw : |(1145140797/2500000000 : ℝ)|=(1145140797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s2_4 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-468930671/2500000000 : ℝ)*x 0 + (5195443201/10000000000 : ℝ)*x 1 + (43670579/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (468930671/2500000000 : ℝ)^4505 ≤ (1146457213961/10000000000000 : ℝ)^3481 := by
    have hnat : (468930671 : ℕ)^4505*10000000000000^3481 ≤ 1146457213961^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468930671 2500000000 1146457213961 10000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195443201/10000000000 : ℝ)^4505 ≤ (42851672122263/100000000000000 : ℝ)^3481 := by
    have hnat : (5195443201 : ℕ)^4505*100000000000000^3481 ≤ 42851672122263^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195443201 10000000000 42851672122263 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43670579/80000000 : ℝ)^4505 ≤ (45683755731459/100000000000000 : ℝ)^3481 := by
    have hnat : (43670579 : ℕ)^4505*100000000000000^3481 ≤ 45683755731459^3481*80000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43670579 80000000 45683755731459 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-468930671/2500000000 : ℝ), (5195443201/10000000000 : ℝ), (43670579/80000000 : ℝ)] ![(1146457213961/10000000000000 : ℝ), (42851672122263/100000000000000 : ℝ), (45683755731459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-468930671/2500000000 : ℝ)|^4505 ≤ (1146457213961/10000000000000 : ℝ)^3481
        have hw : |(-468930671/2500000000 : ℝ)|=(468930671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195443201/10000000000 : ℝ)|^4505 ≤ (42851672122263/100000000000000 : ℝ)^3481
        have hw : |(5195443201/10000000000 : ℝ)|=(5195443201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43670579/80000000 : ℝ)|^4505 ≤ (45683755731459/100000000000000 : ℝ)^3481
        have hw : |(43670579/80000000 : ℝ)|=(43670579/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s2_5 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644441981/5000000000 : ℝ)*x 0 + (-1747995903/10000000000 : ℝ)*x 1 + (2729411499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644441981/5000000000 : ℝ)^4505 ≤ (43851706279393/100000000000000 : ℝ)^3481 := by
    have hnat : (2644441981 : ℕ)^4505*100000000000000^3481 ≤ 43851706279393^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644441981 5000000000 43851706279393 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1747995903/10000000000 : ℝ)^4505 ≤ (209290624617/2000000000000 : ℝ)^3481 := by
    have hnat : (1747995903 : ℕ)^4505*2000000000000^3481 ≤ 209290624617^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1747995903 10000000000 209290624617 2000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729411499/5000000000 : ℝ)^4505 ≤ (2284188123947/5000000000000 : ℝ)^3481 := by
    have hnat : (2729411499 : ℕ)^4505*5000000000000^3481 ≤ 2284188123947^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729411499 5000000000 2284188123947 5000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644441981/5000000000 : ℝ), (-1747995903/10000000000 : ℝ), (2729411499/5000000000 : ℝ)] ![(43851706279393/100000000000000 : ℝ), (209290624617/2000000000000 : ℝ), (2284188123947/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644441981/5000000000 : ℝ)|^4505 ≤ (43851706279393/100000000000000 : ℝ)^3481
        have hw : |(2644441981/5000000000 : ℝ)|=(2644441981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1747995903/10000000000 : ℝ)|^4505 ≤ (209290624617/2000000000000 : ℝ)^3481
        have hw : |(-1747995903/10000000000 : ℝ)|=(1747995903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729411499/5000000000 : ℝ)|^4505 ≤ (2284188123947/5000000000000 : ℝ)^3481
        have hw : |(2729411499/5000000000 : ℝ)|=(2729411499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s2_6 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211555361/400000000 : ℝ)*x 0 + (5458822559/10000000000 : ℝ)*x 1 + (-1747996429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211555361/400000000 : ℝ)^4505 ≤ (10962926738851/25000000000000 : ℝ)^3481 := by
    have hnat : (211555361 : ℕ)^4505*25000000000000^3481 ≤ 10962926738851^3481*400000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211555361 400000000 10962926738851 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458822559/10000000000 : ℝ)^4505 ≤ (22841878862147/50000000000000 : ℝ)^3481 := by
    have hnat : (5458822559 : ℕ)^4505*50000000000000^3481 ≤ 22841878862147^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458822559 10000000000 22841878862147 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1747996429/10000000000 : ℝ)^4505 ≤ (2616133826529/25000000000000 : ℝ)^3481 := by
    have hnat : (1747996429 : ℕ)^4505*25000000000000^3481 ≤ 2616133826529^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1747996429 10000000000 2616133826529 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211555361/400000000 : ℝ), (5458822559/10000000000 : ℝ), (-1747996429/10000000000 : ℝ)] ![(10962926738851/25000000000000 : ℝ), (22841878862147/50000000000000 : ℝ), (2616133826529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211555361/400000000 : ℝ)|^4505 ≤ (10962926738851/25000000000000 : ℝ)^3481
        have hw : |(211555361/400000000 : ℝ)|=(211555361/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458822559/10000000000 : ℝ)|^4505 ≤ (22841878862147/50000000000000 : ℝ)^3481
        have hw : |(5458822559/10000000000 : ℝ)|=(5458822559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1747996429/10000000000 : ℝ)|^4505 ≤ (2616133826529/25000000000000 : ℝ)^3481
        have hw : |(-1747996429/10000000000 : ℝ)|=(1747996429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s2_7 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067724689/2500000000 : ℝ)*x 0 + (2288384931/5000000000 : ℝ)*x 1 + (99572437/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067724689/2500000000 : ℝ)^4505 ≤ (16626458346769/50000000000000 : ℝ)^3481 := by
    have hnat : (1067724689 : ℕ)^4505*50000000000000^3481 ≤ 16626458346769^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067724689 2500000000 16626458346769 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288384931/5000000000 : ℝ)^4505 ≤ (36366901533449/100000000000000 : ℝ)^3481 := by
    have hnat : (2288384931 : ℕ)^4505*100000000000000^3481 ≤ 36366901533449^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288384931 5000000000 36366901533449 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99572437/250000000 : ℝ)^4505 ≤ (15190090881983/50000000000000 : ℝ)^3481 := by
    have hnat : (99572437 : ℕ)^4505*50000000000000^3481 ≤ 15190090881983^3481*250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99572437 250000000 15190090881983 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067724689/2500000000 : ℝ), (2288384931/5000000000 : ℝ), (99572437/250000000 : ℝ)] ![(16626458346769/50000000000000 : ℝ), (36366901533449/100000000000000 : ℝ), (15190090881983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067724689/2500000000 : ℝ)|^4505 ≤ (16626458346769/50000000000000 : ℝ)^3481
        have hw : |(1067724689/2500000000 : ℝ)|=(1067724689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2288384931/5000000000 : ℝ)|^4505 ≤ (36366901533449/100000000000000 : ℝ)^3481
        have hw : |(2288384931/5000000000 : ℝ)|=(2288384931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(99572437/250000000 : ℝ)|^4505 ≤ (15190090881983/50000000000000 : ℝ)^3481
        have hw : |(99572437/250000000 : ℝ)|=(99572437/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1504_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1031/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5191/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16027/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (921/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1031/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (921/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1031/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (921/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1031/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (921/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1031/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (921/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1031/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (921/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1031/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1031/12500 : ℝ) ^ (4503/1024 : ℝ) ≤ (858332452242491/50000000000000000000 : ℝ) := by
    have hpowers : (1031/12500 : ℝ)^4503 ≤ (858332452242491/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1031 : ℕ)^4503*50000000000000000000^1024 ≤ 858332452242491^1024*12500^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1031 12500 858332452242491 50000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1031/12500 : ℝ)) (X := (858332452242491/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (921/5000 : ℝ) ^ (4503/1024 : ℝ) ≤ (58767853632548473/100000000000000000000 : ℝ) := by
    have hpowers : (921/5000 : ℝ)^4503 ≤ (58767853632548473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (921 : ℕ)^4503*100000000000000000000^1024 ≤ 58767853632548473^1024*5000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        921 5000 58767853632548473 100000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (921/5000 : ℝ)) (X := (58767853632548473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000858332452242491/25000000000000000000 : ℝ) ≤ (5000039037120771/5000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (25000858332452242491/25000000000000000000 : ℝ)^1024 ≤ (5000039037120771/5000000000000000 : ℝ)^4503 := by
      have hnat : (25000858332452242491 : ℕ)^1024*5000000000000000^4503 ≤ 5000039037120771^4503*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000858332452242491 25000000000000000000 5000039037120771 5000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000039037120771/5000000000000000 : ℝ)) (X := (25000858332452242491/25000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20012096903707406691/20000000000000000000 : ℝ) ≤ (10001375120602707/10000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (20012096903707406691/20000000000000000000 : ℝ)^1024 ≤ (10001375120602707/10000000000000000 : ℝ)^4503 := by
      have hnat : (20012096903707406691 : ℕ)^1024*10000000000000000^4503 ≤ 10001375120602707^4503*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20012096903707406691 20000000000000000000 10001375120602707 10000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001375120602707/10000000000000000 : ℝ)) (X := (20012096903707406691/20000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50058767853632548473/50000000000000000000 : ℝ) ≤ (312583505217621/312500000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (50058767853632548473/50000000000000000000 : ℝ)^1024 ≤ (312583505217621/312500000000000 : ℝ)^4503 := by
      have hnat : (50058767853632548473 : ℕ)^1024*312500000000000^4503 ≤ 312583505217621^4503*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50058767853632548473 50000000000000000000 312583505217621 312500000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312583505217621/312500000000000 : ℝ)) (X := (50058767853632548473/50000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(858332452242491/50000000000000000000 : ℝ) ≤ ((12712424761801398423/12715000000000000000 : ℝ)+2*(259409272233/203440000000000 : ℝ)*(1031/12500 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (12712424761801398423/12715000000000000000 : ℝ)+2*(259409272233/203440000000000 : ℝ)*(1031/12500 : ℝ)=(5000039037120771/5000000000000000 : ℝ) by norm_num, show 1+2*(858332452242491/50000000000000000000 : ℝ)=(25000858332452242491/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(58767853632548473/100000000000000000000 : ℝ)+(858332452242491/50000000000000000000 : ℝ) ≤ ((12712424761801398423/12715000000000000000 : ℝ)+(259409272233/203440000000000 : ℝ)*((921/5000 : ℝ)+(1031/12500 : ℝ)))^(4503/1024 : ℝ) := by
    rw [show (12712424761801398423/12715000000000000000 : ℝ)+(259409272233/203440000000000 : ℝ)*((921/5000 : ℝ)+(1031/12500 : ℝ))=(10001375120602707/10000000000000000 : ℝ) by norm_num, show 1+(58767853632548473/100000000000000000000 : ℝ)+(858332452242491/50000000000000000000 : ℝ)=(20012096903707406691/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(58767853632548473/100000000000000000000 : ℝ) ≤ ((12712424761801398423/12715000000000000000 : ℝ)+2*(259409272233/203440000000000 : ℝ)*(921/5000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (12712424761801398423/12715000000000000000 : ℝ)+2*(259409272233/203440000000000 : ℝ)*(921/5000 : ℝ)=(312583505217621/312500000000000 : ℝ) by norm_num, show 1+2*(58767853632548473/100000000000000000000 : ℝ)=(50058767853632548473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12712424761801398423/12715000000000000000 : ℝ)*(X 1 0+X 2 0)+(259409272233/203440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (1031/12500 : ℝ)) (hi := (921/5000 : ℝ)) (c := (12712424761801398423/12715000000000000000 : ℝ)) (alpha := (259409272233/203440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12712424761801398423/12715000000000000000 : ℝ)*(X 0 1+X 2 1)+(259409272233/203440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (1031/12500 : ℝ)) (hi := (921/5000 : ℝ)) (c := (12712424761801398423/12715000000000000000 : ℝ)) (alpha := (259409272233/203440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12712424761801398423/12715000000000000000 : ℝ)*(X 0 2+X 1 2)+(259409272233/203440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (1031/12500 : ℝ)) (hi := (921/5000 : ℝ)) (c := (12712424761801398423/12715000000000000000 : ℝ)) (alpha := (259409272233/203440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-937834627/5000000000 : ℝ)*X 0 0+(5460519883/10000000000 : ℝ)*X 0 1+(1298440063/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358845661/10000000000 : ℝ)*X 1 0+(-1006529/5000000 : ℝ)*X 1 1+(519376117/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679423299/5000000000 : ℝ)*X 2 0+(2596880267/5000000000 : ℝ)*X 2 1+(-251632199/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((170831019/400000000 : ℝ)*X 0 0+(3979070667/10000000000 : ℝ)*X 0 1+(1145140797/2500000000 : ℝ)*X 0 2+(170831019/400000000 : ℝ)*X 1 0+(3979070667/10000000000 : ℝ)*X 1 1+(1145140797/2500000000 : ℝ)*X 1 2+(170831019/400000000 : ℝ)*X 2 0+(3979070667/10000000000 : ℝ)*X 2 1+(1145140797/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-468930671/2500000000 : ℝ)*X 0 0+(5195443201/10000000000 : ℝ)*X 0 1+(43670579/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644441981/5000000000 : ℝ)*X 1 0+(-1747995903/10000000000 : ℝ)*X 1 1+(2729411499/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211555361/400000000 : ℝ)*X 2 0+(5458822559/10000000000 : ℝ)*X 2 1+(-1747996429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1067724689/2500000000 : ℝ)*X 0 0+(2288384931/5000000000 : ℝ)*X 0 1+(99572437/250000000 : ℝ)*X 0 2+(1067724689/2500000000 : ℝ)*X 1 0+(2288384931/5000000000 : ℝ)*X 1 1+(99572437/250000000 : ℝ)*X 1 2+(1067724689/2500000000 : ℝ)*X 2 0+(2288384931/5000000000 : ℝ)*X 2 1+(99572437/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2777822117422384723541204517/635750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (234590273/25000000000000 : ℝ)*(base19) + (75813913/6250000000000 : ℝ)*(base23) + (67828891/100000000000000 : ℝ)*(upper3) + (102034851/50000000000000 : ℝ)*(upper4) + (47745307/20000000000000 : ℝ)*(upper5) + (2705645069390593/100000000000000 : ℝ)*(major0) + (2705645069390593/100000000000000 : ℝ)*(major1) + (2705645069390593/100000000000000 : ℝ)*(major2) + (1874354920248891/50000000000000 : ℝ)*(sp0) + (749747268227207/20000000000000 : ℝ)*(sp1) + (3748736066474519/100000000000000 : ℝ)*(sp2) + (16625415066513/1000000000000 : ℝ)*(sp3) + (5487799869/20000000000000 : ℝ)*(sp4) + (560349367/5000000000000 : ℝ)*(sp7) + (1662552713638639/100000000000000 : ℝ)*(f.failure) + (1874368639748563/50000000000000 : ℝ)*(f.sum) + (8779943672827/2034400000000000000000000000 : ℝ)*base66 + (5019347966104702661/1271500000000000000000000000000000 : ℝ)*base68 + (458841125276702661/1271500000000000000000000000000000 : ℝ)*base70 + (3479302540549297339/1271500000000000000000000000000000 : ℝ)*base71 + (59254904174791/10172000000000000000000000000 : ℝ)*base74 + (13337426607513202661/1271500000000000000000000000000000 : ℝ)*base76 + (2174308398918797339/1271500000000000000000000000000000 : ℝ)*base77 + (6095965536197202661/1271500000000000000000000000000000 : ℝ)*base80 + (82647264167/16275200000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3071911/1250000000000000000000 : ℝ)*base90 + (3071911/1250000000000000000000 : ℝ)*base92 + (3071911/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1190963677811034024296011221/317875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3807609/12500000000000 : ℝ)*(base23) + (115504701/100000000000000 : ℝ)*(lower2) + (71755399/100000000000000 : ℝ)*(upper3) + (146128421/100000000000000 : ℝ)*(lower4) + (1370168912691597/50000000000000 : ℝ)*(major0) + (1370168912691597/50000000000000 : ℝ)*(major1) + (1370168912691597/50000000000000 : ℝ)*(major2) + (1243374423/20000000000000 : ℝ)*(sp1) + (45212569/6250000000000 : ℝ)*(sp2) + (3340226043/100000000000000 : ℝ)*(sp3) + (759360992457059/20000000000000 : ℝ)*(sp4) + (189839937270659/5000000000000 : ℝ)*(sp5) + (94920105210583/2500000000000 : ℝ)*(sp6) + (841933611683493/50000000000000 : ℝ)*(sp7) + (420967640898257/25000000000000 : ℝ)*(f.failure) + (759360992457059/20000000000000 : ℝ)*(f.sum) + (138373204429/1017200000000000000000000000 : ℝ)*base66 + (605170329391464031/635750000000000000000000000000000 : ℝ)*base67 + (9097906585395714031/635750000000000000000000000000000 : ℝ)*base69 + (3805255394980464031/635750000000000000000000000000000 : ℝ)*base71 + (961688555177/5086000000000000000000000000 : ℝ)*base74 + (32357897196964031/635750000000000000000000000000000 : ℝ)*base75 + (25725759625422714031/635750000000000000000000000000000 : ℝ)*base77 + (10831287835465714031/635750000000000000000000000000000 : ℝ)*base79 + (137971967291/203440000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2416393/312500000000000000000 : ℝ)*base90 + (2416393/312500000000000000000 : ℝ)*base92 + (2416393/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1504_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1031/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1504_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1504_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1504_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1504_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1504_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1504_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
