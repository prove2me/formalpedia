-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1621_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:58:12.850047+00:00
-- url     : https://prove2.me/submissions/cd3ac840-fa8c-4452-ab1d-7b5c01632f3a

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
theorem support_rectangle_w1621_s0_0 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1544937039/10000000000 : ℝ)*x 0 + (5822407271/10000000000 : ℝ)*x 1 + (4901141519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1544937039/10000000000 : ℝ)^4803 ≤ (4656922463977/50000000000000 : ℝ)^3779 := by
    have hnat : (1544937039 : ℕ)^4803*50000000000000^3779 ≤ 4656922463977^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544937039 10000000000 4656922463977 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5822407271/10000000000 : ℝ)^4803 ≤ (1571455824167/3125000000000 : ℝ)^3779 := by
    have hnat : (5822407271 : ℕ)^4803*3125000000000^3779 ≤ 1571455824167^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5822407271 10000000000 1571455824167 3125000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4901141519/10000000000 : ℝ)^4803 ≤ (631243260787/1562500000000 : ℝ)^3779 := by
    have hnat : (4901141519 : ℕ)^4803*1562500000000^3779 ≤ 631243260787^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4901141519 10000000000 631243260787 1562500000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1544937039/10000000000 : ℝ), (5822407271/10000000000 : ℝ), (4901141519/10000000000 : ℝ)] ![(4656922463977/50000000000000 : ℝ), (1571455824167/3125000000000 : ℝ), (631243260787/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1544937039/10000000000 : ℝ)|^4803 ≤ (4656922463977/50000000000000 : ℝ)^3779
        have hw : |(-1544937039/10000000000 : ℝ)|=(1544937039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5822407271/10000000000 : ℝ)|^4803 ≤ (1571455824167/3125000000000 : ℝ)^3779
        have hw : |(5822407271/10000000000 : ℝ)|=(5822407271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4901141519/10000000000 : ℝ)|^4803 ≤ (631243260787/1562500000000 : ℝ)^3779
        have hw : |(4901141519/10000000000 : ℝ)|=(4901141519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s0_1 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272460289/500000000 : ℝ)*x 0 + (-513441837/2500000000 : ℝ)*x 1 + (196045673/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272460289/500000000 : ℝ)^4803 ≤ (46226084968721/100000000000000 : ℝ)^3779 := by
    have hnat : (272460289 : ℕ)^4803*100000000000000^3779 ≤ 46226084968721^3779*500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272460289 500000000 46226084968721 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513441837/2500000000 : ℝ)^4803 ≤ (1671792889651/12500000000000 : ℝ)^3779 := by
    have hnat : (513441837 : ℕ)^4803*12500000000000^3779 ≤ 1671792889651^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513441837 2500000000 1671792889651 12500000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196045673/400000000 : ℝ)^4803 ≤ (4039957189617/10000000000000 : ℝ)^3779 := by
    have hnat : (196045673 : ℕ)^4803*10000000000000^3779 ≤ 4039957189617^3779*400000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196045673 400000000 4039957189617 10000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272460289/500000000 : ℝ), (-513441837/2500000000 : ℝ), (196045673/400000000 : ℝ)] ![(46226084968721/100000000000000 : ℝ), (1671792889651/12500000000000 : ℝ), (4039957189617/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272460289/500000000 : ℝ)|^4803 ≤ (46226084968721/100000000000000 : ℝ)^3779
        have hw : |(272460289/500000000 : ℝ)|=(272460289/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513441837/2500000000 : ℝ)|^4803 ≤ (1671792889651/12500000000000 : ℝ)^3779
        have hw : |(-513441837/2500000000 : ℝ)|=(513441837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(196045673/400000000 : ℝ)|^4803 ≤ (4039957189617/10000000000000 : ℝ)^3779
        have hw : |(196045673/400000000 : ℝ)|=(196045673/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s0_2 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2724602763/5000000000 : ℝ)*x 0 + (153160679/312500000 : ℝ)*x 1 + (-1026883901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2724602763/5000000000 : ℝ)^4803 ≤ (23113041115077/50000000000000 : ℝ)^3779 := by
    have hnat : (2724602763 : ℕ)^4803*50000000000000^3779 ≤ 23113041115077^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724602763 5000000000 23113041115077 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153160679/312500000 : ℝ)^4803 ≤ (40399570879951/100000000000000 : ℝ)^3779 := by
    have hnat : (153160679 : ℕ)^4803*100000000000000^3779 ≤ 40399570879951^3779*312500000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153160679 312500000 40399570879951 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026883901/5000000000 : ℝ)^4803 ≤ (13374346874827/100000000000000 : ℝ)^3779 := by
    have hnat : (1026883901 : ℕ)^4803*100000000000000^3779 ≤ 13374346874827^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026883901 5000000000 13374346874827 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2724602763/5000000000 : ℝ), (153160679/312500000 : ℝ), (-1026883901/5000000000 : ℝ)] ![(23113041115077/50000000000000 : ℝ), (40399570879951/100000000000000 : ℝ), (13374346874827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2724602763/5000000000 : ℝ)|^4803 ≤ (23113041115077/50000000000000 : ℝ)^3779
        have hw : |(2724602763/5000000000 : ℝ)|=(2724602763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(153160679/312500000 : ℝ)|^4803 ≤ (40399570879951/100000000000000 : ℝ)^3779
        have hw : |(153160679/312500000 : ℝ)|=(153160679/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026883901/5000000000 : ℝ)|^4803 ≤ (13374346874827/100000000000000 : ℝ)^3779
        have hw : |(-1026883901/5000000000 : ℝ)|=(1026883901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s0_3 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16032883/39062500 : ℝ)*x 0 + (3076229513/10000000000 : ℝ)*x 1 + (1343230153/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16032883/39062500 : ℝ)^4803 ≤ (32244372107299/100000000000000 : ℝ)^3779 := by
    have hnat : (16032883 : ℕ)^4803*100000000000000^3779 ≤ 32244372107299^3779*39062500^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16032883 39062500 32244372107299 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3076229513/10000000000 : ℝ)^4803 ≤ (22350465813129/100000000000000 : ℝ)^3779 := by
    have hnat : (3076229513 : ℕ)^4803*100000000000000^3779 ≤ 22350465813129^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3076229513 10000000000 22350465813129 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343230153/2500000000 : ℝ)^4803 ≤ (22702581034451/50000000000000 : ℝ)^3779 := by
    have hnat : (1343230153 : ℕ)^4803*50000000000000^3779 ≤ 22702581034451^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343230153 2500000000 22702581034451 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16032883/39062500 : ℝ), (3076229513/10000000000 : ℝ), (1343230153/2500000000 : ℝ)] ![(32244372107299/100000000000000 : ℝ), (22350465813129/100000000000000 : ℝ), (22702581034451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16032883/39062500 : ℝ)|^4803 ≤ (32244372107299/100000000000000 : ℝ)^3779
        have hw : |(16032883/39062500 : ℝ)|=(16032883/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3076229513/10000000000 : ℝ)|^4803 ≤ (22350465813129/100000000000000 : ℝ)^3779
        have hw : |(3076229513/10000000000 : ℝ)|=(3076229513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343230153/2500000000 : ℝ)|^4803 ≤ (22702581034451/50000000000000 : ℝ)^3779
        have hw : |(1343230153/2500000000 : ℝ)|=(1343230153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s0_4 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1547584883/10000000000 : ℝ)*x 0 + (2462168673/5000000000 : ℝ)*x 1 + (1449598227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1547584883/10000000000 : ℝ)^4803 ≤ (9334137967391/100000000000000 : ℝ)^3779 := by
    have hnat : (1547584883 : ℕ)^4803*100000000000000^3779 ≤ 9334137967391^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1547584883 10000000000 9334137967391 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2462168673/5000000000 : ℝ)^4803 ≤ (40642734835613/100000000000000 : ℝ)^3779 := by
    have hnat : (2462168673 : ℕ)^4803*100000000000000^3779 ≤ 40642734835613^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462168673 5000000000 40642734835613 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1449598227/2500000000 : ℝ)^4803 ≤ (10004625437891/20000000000000 : ℝ)^3779 := by
    have hnat : (1449598227 : ℕ)^4803*20000000000000^3779 ≤ 10004625437891^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449598227 2500000000 10004625437891 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1547584883/10000000000 : ℝ), (2462168673/5000000000 : ℝ), (1449598227/2500000000 : ℝ)] ![(9334137967391/100000000000000 : ℝ), (40642734835613/100000000000000 : ℝ), (10004625437891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1547584883/10000000000 : ℝ)|^4803 ≤ (9334137967391/100000000000000 : ℝ)^3779
        have hw : |(-1547584883/10000000000 : ℝ)|=(1547584883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2462168673/5000000000 : ℝ)|^4803 ≤ (40642734835613/100000000000000 : ℝ)^3779
        have hw : |(2462168673/5000000000 : ℝ)|=(2462168673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1449598227/2500000000 : ℝ)|^4803 ≤ (10004625437891/20000000000000 : ℝ)^3779
        have hw : |(1449598227/2500000000 : ℝ)|=(1449598227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s0_5 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519763161/1000000000 : ℝ)*x 0 + (-578258199/5000000000 : ℝ)*x 1 + (1159678583/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519763161/1000000000 : ℝ)^4803 ≤ (10882708337099/25000000000000 : ℝ)^3779 := by
    have hnat : (519763161 : ℕ)^4803*25000000000000^3779 ≤ 10882708337099^3779*1000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519763161 1000000000 10882708337099 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (578258199/5000000000 : ℝ)^4803 ≤ (6446039366043/100000000000000 : ℝ)^3779 := by
    have hnat : (578258199 : ℕ)^4803*100000000000000^3779 ≤ 6446039366043^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578258199 5000000000 6446039366043 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1159678583/2000000000 : ℝ)^4803 ≤ (1563222727069/3125000000000 : ℝ)^3779 := by
    have hnat : (1159678583 : ℕ)^4803*3125000000000^3779 ≤ 1563222727069^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159678583 2000000000 1563222727069 3125000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519763161/1000000000 : ℝ), (-578258199/5000000000 : ℝ), (1159678583/2000000000 : ℝ)] ![(10882708337099/25000000000000 : ℝ), (6446039366043/100000000000000 : ℝ), (1563222727069/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519763161/1000000000 : ℝ)|^4803 ≤ (10882708337099/25000000000000 : ℝ)^3779
        have hw : |(519763161/1000000000 : ℝ)|=(519763161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-578258199/5000000000 : ℝ)|^4803 ≤ (6446039366043/100000000000000 : ℝ)^3779
        have hw : |(-578258199/5000000000 : ℝ)|=(578258199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1159678583/2000000000 : ℝ)|^4803 ≤ (1563222727069/3125000000000 : ℝ)^3779
        have hw : |(1159678583/2000000000 : ℝ)|=(1159678583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s0_6 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299407893/2500000000 : ℝ)*x 0 + (2899196687/5000000000 : ℝ)*x 1 + (-578257873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299407893/2500000000 : ℝ)^4803 ≤ (43530832943903/100000000000000 : ℝ)^3779 := by
    have hnat : (1299407893 : ℕ)^4803*100000000000000^3779 ≤ 43530832943903^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299407893 2500000000 43530832943903 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2899196687/5000000000 : ℝ)^4803 ≤ (5002313229903/10000000000000 : ℝ)^3779 := by
    have hnat : (2899196687 : ℕ)^4803*10000000000000^3779 ≤ 5002313229903^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2899196687 5000000000 5002313229903 10000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (578257873/5000000000 : ℝ)^4803 ≤ (3223017373647/50000000000000 : ℝ)^3779 := by
    have hnat : (578257873 : ℕ)^4803*50000000000000^3779 ≤ 3223017373647^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578257873 5000000000 3223017373647 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299407893/2500000000 : ℝ), (2899196687/5000000000 : ℝ), (-578257873/5000000000 : ℝ)] ![(43530832943903/100000000000000 : ℝ), (5002313229903/10000000000000 : ℝ), (3223017373647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299407893/2500000000 : ℝ)|^4803 ≤ (43530832943903/100000000000000 : ℝ)^3779
        have hw : |(1299407893/2500000000 : ℝ)|=(1299407893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2899196687/5000000000 : ℝ)|^4803 ≤ (5002313229903/10000000000000 : ℝ)^3779
        have hw : |(2899196687/5000000000 : ℝ)|=(2899196687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-578257873/5000000000 : ℝ)|^4803 ≤ (3223017373647/50000000000000 : ℝ)^3779
        have hw : |(-578257873/5000000000 : ℝ)|=(578257873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s0_7 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4111018653/10000000000 : ℝ)*x 0 + (5315092141/10000000000 : ℝ)*x 1 + (3136097289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4111018653/10000000000 : ℝ)^4803 ≤ (16155145989471/50000000000000 : ℝ)^3779 := by
    have hnat : (4111018653 : ℕ)^4803*50000000000000^3779 ≤ 16155145989471^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111018653 10000000000 16155145989471 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5315092141/10000000000 : ℝ)^4803 ≤ (44784954898043/100000000000000 : ℝ)^3779 := by
    have hnat : (5315092141 : ℕ)^4803*100000000000000^3779 ≤ 44784954898043^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5315092141 10000000000 44784954898043 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3136097289/10000000000 : ℝ)^4803 ≤ (22904753106339/100000000000000 : ℝ)^3779 := by
    have hnat : (3136097289 : ℕ)^4803*100000000000000^3779 ≤ 22904753106339^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3136097289 10000000000 22904753106339 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4111018653/10000000000 : ℝ), (5315092141/10000000000 : ℝ), (3136097289/10000000000 : ℝ)] ![(16155145989471/50000000000000 : ℝ), (44784954898043/100000000000000 : ℝ), (22904753106339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4111018653/10000000000 : ℝ)|^4803 ≤ (16155145989471/50000000000000 : ℝ)^3779
        have hw : |(4111018653/10000000000 : ℝ)|=(4111018653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5315092141/10000000000 : ℝ)|^4803 ≤ (44784954898043/100000000000000 : ℝ)^3779
        have hw : |(5315092141/10000000000 : ℝ)|=(5315092141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3136097289/10000000000 : ℝ)|^4803 ≤ (22904753106339/100000000000000 : ℝ)^3779
        have hw : |(3136097289/10000000000 : ℝ)|=(3136097289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1621_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2129/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2999/12500 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4799/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4799 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4799*1^1024 ≤ 0^1024*1^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4799/1024 : ℝ) ≤ (682361989836792413/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4799 ≤ (682361989836792413/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4799*50000000000000000000^1024 ≤ 682361989836792413^1024*5^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 682361989836792413 50000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (682361989836792413/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4799 := by
      have hnat : (1 : ℕ)^1024*1^4799 ≤ 1^4799*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50682361989836792413/50000000000000000000 : ℝ) ≤ (5014482565450113/5000000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (50682361989836792413/50000000000000000000 : ℝ)^1024 ≤ (5014482565450113/5000000000000000 : ℝ)^4799 := by
      have hnat : (50682361989836792413 : ℕ)^1024*5000000000000000^4799 ≤ 5014482565450113^4799*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50682361989836792413 50000000000000000000 5014482565450113 5000000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014482565450113/5000000000000000 : ℝ)) (X := (50682361989836792413/50000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25682361989836792413/25000000000000000000 : ℝ) ≤ (2514482565450113/2500000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (25682361989836792413/25000000000000000000 : ℝ)^1024 ≤ (2514482565450113/2500000000000000 : ℝ)^4799 := by
      have hnat : (25682361989836792413 : ℕ)^1024*2500000000000000^4799 ≤ 2514482565450113^4799*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25682361989836792413 25000000000000000000 2514482565450113 2500000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514482565450113/2500000000000000 : ℝ)) (X := (25682361989836792413/25000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14482565450113/2000000000000000 : ℝ)*(0 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14482565450113/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(682361989836792413/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14482565450113/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4799/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14482565450113/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5014482565450113/5000000000000000 : ℝ) by norm_num, show 1+(682361989836792413/50000000000000000000 : ℝ)+(0 : ℝ)=(50682361989836792413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(682361989836792413/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14482565450113/2000000000000000 : ℝ)*(2/5 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14482565450113/2000000000000000 : ℝ)*(2/5 : ℝ)=(2514482565450113/2500000000000000 : ℝ) by norm_num, show 1+2*(682361989836792413/50000000000000000000 : ℝ)=(25682361989836792413/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14482565450113/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14482565450113/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14482565450113/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14482565450113/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14482565450113/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14482565450113/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1544937039/10000000000 : ℝ)*X 0 0+(5822407271/10000000000 : ℝ)*X 0 1+(4901141519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((272460289/500000000 : ℝ)*X 1 0+(-513441837/2500000000 : ℝ)*X 1 1+(196045673/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2724602763/5000000000 : ℝ)*X 2 0+(153160679/312500000 : ℝ)*X 2 1+(-1026883901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((16032883/39062500 : ℝ)*X 0 0+(3076229513/10000000000 : ℝ)*X 0 1+(1343230153/2500000000 : ℝ)*X 0 2+(16032883/39062500 : ℝ)*X 1 0+(3076229513/10000000000 : ℝ)*X 1 1+(1343230153/2500000000 : ℝ)*X 1 2+(16032883/39062500 : ℝ)*X 2 0+(3076229513/10000000000 : ℝ)*X 2 1+(1343230153/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1547584883/10000000000 : ℝ)*X 0 0+(2462168673/5000000000 : ℝ)*X 0 1+(1449598227/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((519763161/1000000000 : ℝ)*X 1 0+(-578258199/5000000000 : ℝ)*X 1 1+(1159678583/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1299407893/2500000000 : ℝ)*X 2 0+(2899196687/5000000000 : ℝ)*X 2 1+(-578257873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4111018653/10000000000 : ℝ)*X 0 0+(5315092141/10000000000 : ℝ)*X 0 1+(3136097289/10000000000 : ℝ)*X 0 2+(4111018653/10000000000 : ℝ)*X 1 0+(5315092141/10000000000 : ℝ)*X 1 1+(3136097289/10000000000 : ℝ)*X 1 2+(4111018653/10000000000 : ℝ)*X 2 0+(5315092141/10000000000 : ℝ)*X 2 1+(3136097289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106217215650242898204291/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1081562083/100000000000000 : ℝ)*(base19) + (969058339/100000000000000 : ℝ)*(base23) + (4012513/1562500000000 : ℝ)*(upper3) + (16867323/50000000000000 : ℝ)*(upper4) + (11373/25000000000 : ℝ)*(upper5) + (760442470656831/100000000000000 : ℝ)*(major0) + (760442470656831/100000000000000 : ℝ)*(major1) + (760442470656831/100000000000000 : ℝ)*(major2) + (86837451721/8000000000 : ℝ)*(sp0) + (217094143861667/20000000000000 : ℝ)*(sp1) + (542735415906039/50000000000000 : ℝ)*(sp2) + (435410624847549/100000000000000 : ℝ)*(sp3) + (1827178959/50000000000000 : ℝ)*(sp4) + (584641749/25000000000000 : ℝ)*(sp7) + (217706481707273/50000000000000 : ℝ)*(f.failure) + (542735900435209/50000000000000 : ℝ)*(f.sum) + (357876308571903/100000000000000000000000000000 : ℝ)*base65 + (720890767028097/200000000000000000000000000000 : ℝ)*base68 + (887928897971903/200000000000000000000000000000 : ℝ)*base69 + (10542865171903/200000000000000000000000000000 : ℝ)*base71 + (46061623871903/100000000000000000000000000000 : ℝ)*base73 + (505473231771903/200000000000000000000000000000 : ℝ)*base75 + (941149519571903/200000000000000000000000000000 : ℝ)*base77 + (1121189701771903/200000000000000000000000000000 : ℝ)*base79 + (332532145571903/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (262211/62500000000000000000 : ℝ)*base89 + (262211/62500000000000000000 : ℝ)*base91 + (262211/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7699908564507915599571/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (25479389/1250000000000 : ℝ)*(base19) + (1120178247/50000000000000 : ℝ)*(base23) + (49724941/25000000000000 : ℝ)*(base39) + (136059527/50000000000000 : ℝ)*(upper3) + (99084181/25000000000000 : ℝ)*(upper5) + (400754561619953/50000000000000 : ℝ)*(major0) + (400754561619953/50000000000000 : ℝ)*(major1) + (801508924340143/100000000000000 : ℝ)*(major2) + (815152061/12500000000000 : ℝ)*(sp1) + (1363090007/20000000000000 : ℝ)*(sp2) + (286022718942949/25000000000000 : ℝ)*(sp4) + (1144082316204187/100000000000000 : ℝ)*(sp5) + (1144082018865031/100000000000000 : ℝ)*(sp6) + (91785368655763/20000000000000 : ℝ)*(sp7) + (91785368655763/20000000000000 : ℝ)*(f.failure) + (28602276866789/2500000000000 : ℝ)*(f.sum) + (324679181804463/200000000000000000000000000000 : ℝ)*base66 + (989348956413841/200000000000000000000000000000 : ℝ)*base68 + (141931643395311/100000000000000000000000000000 : ℝ)*base70 + (760669271213841/200000000000000000000000000000 : ℝ)*base72 + (105784049404463/200000000000000000000000000000 : ℝ)*base74 + (272296062904689/100000000000000000000000000000 : ℝ)*base75 + (1064984946795311/100000000000000000000000000000 : ℝ)*base78 + (954041911995311/100000000000000000000000000000 : ℝ)*base80 + (104134819954689/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (295641/25000000000000000000 : ℝ)*base89 + (295641/25000000000000000000 : ℝ)*base91 + (45641/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1621_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2129/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2999/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1621_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1621_s1_0 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-415830291/2500000000 : ℝ)*x 0 + (275994863/500000000 : ℝ)*x 1 + (5126985319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415830291/2500000000 : ℝ)^4803 ≤ (10230176111397/100000000000000 : ℝ)^3779 := by
    have hnat : (415830291 : ℕ)^4803*100000000000000^3779 ≤ 10230176111397^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415830291 2500000000 10230176111397 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275994863/500000000 : ℝ)^4803 ≤ (11747399714911/25000000000000 : ℝ)^3779 := by
    have hnat : (275994863 : ℕ)^4803*25000000000000^3779 ≤ 11747399714911^3779*500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275994863 500000000 11747399714911 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5126985319/10000000000 : ℝ)^4803 ≤ (21390112505011/50000000000000 : ℝ)^3779 := by
    have hnat : (5126985319 : ℕ)^4803*50000000000000^3779 ≤ 21390112505011^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126985319 10000000000 21390112505011 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415830291/2500000000 : ℝ), (275994863/500000000 : ℝ), (5126985319/10000000000 : ℝ)] ![(10230176111397/100000000000000 : ℝ), (11747399714911/25000000000000 : ℝ), (21390112505011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415830291/2500000000 : ℝ)|^4803 ≤ (10230176111397/100000000000000 : ℝ)^3779
        have hw : |(-415830291/2500000000 : ℝ)|=(415830291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(275994863/500000000 : ℝ)|^4803 ≤ (11747399714911/25000000000000 : ℝ)^3779
        have hw : |(275994863/500000000 : ℝ)|=(275994863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5126985319/10000000000 : ℝ)|^4803 ≤ (21390112505011/50000000000000 : ℝ)^3779
        have hw : |(5126985319/10000000000 : ℝ)|=(5126985319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s1_1 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342182217/2500000000 : ℝ)*x 0 + (-116777543/625000000 : ℝ)*x 1 + (2563492561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342182217/2500000000 : ℝ)^4803 ≤ (9072028956009/20000000000000 : ℝ)^3779 := by
    have hnat : (1342182217 : ℕ)^4803*20000000000000^3779 ≤ 9072028956009^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342182217 2500000000 9072028956009 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116777543/625000000 : ℝ)^4803 ≤ (11859632292231/100000000000000 : ℝ)^3779 := by
    have hnat : (116777543 : ℕ)^4803*100000000000000^3779 ≤ 11859632292231^3779*625000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116777543 625000000 11859632292231 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2563492561/5000000000 : ℝ)^4803 ≤ (42780222920809/100000000000000 : ℝ)^3779 := by
    have hnat : (2563492561 : ℕ)^4803*100000000000000^3779 ≤ 42780222920809^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563492561 5000000000 42780222920809 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342182217/2500000000 : ℝ), (-116777543/625000000 : ℝ), (2563492561/5000000000 : ℝ)] ![(9072028956009/20000000000000 : ℝ), (11859632292231/100000000000000 : ℝ), (42780222920809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342182217/2500000000 : ℝ)|^4803 ≤ (9072028956009/20000000000000 : ℝ)^3779
        have hw : |(1342182217/2500000000 : ℝ)|=(1342182217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-116777543/625000000 : ℝ)|^4803 ≤ (11859632292231/100000000000000 : ℝ)^3779
        have hw : |(-116777543/625000000 : ℝ)|=(116777543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2563492561/5000000000 : ℝ)|^4803 ≤ (42780222920809/100000000000000 : ℝ)^3779
        have hw : |(2563492561/5000000000 : ℝ)|=(2563492561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s1_2 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684364547/5000000000 : ℝ)*x 0 + (5126984779/10000000000 : ℝ)*x 1 + (-1868440837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684364547/5000000000 : ℝ)^4803 ≤ (22680073603459/50000000000000 : ℝ)^3779 := by
    have hnat : (2684364547 : ℕ)^4803*50000000000000^3779 ≤ 22680073603459^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684364547 5000000000 22680073603459 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5126984779/10000000000 : ℝ)^4803 ≤ (42780219283243/100000000000000 : ℝ)^3779 := by
    have hnat : (5126984779 : ℕ)^4803*100000000000000^3779 ≤ 42780219283243^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126984779 10000000000 42780219283243 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1868440837/10000000000 : ℝ)^4803 ≤ (11859633494257/100000000000000 : ℝ)^3779 := by
    have hnat : (1868440837 : ℕ)^4803*100000000000000^3779 ≤ 11859633494257^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868440837 10000000000 11859633494257 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684364547/5000000000 : ℝ), (5126984779/10000000000 : ℝ), (-1868440837/10000000000 : ℝ)] ![(22680073603459/50000000000000 : ℝ), (42780219283243/100000000000000 : ℝ), (11859633494257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684364547/5000000000 : ℝ)|^4803 ≤ (22680073603459/50000000000000 : ℝ)^3779
        have hw : |(2684364547/5000000000 : ℝ)|=(2684364547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5126984779/10000000000 : ℝ)|^4803 ≤ (42780219283243/100000000000000 : ℝ)^3779
        have hw : |(5126984779/10000000000 : ℝ)|=(5126984779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1868440837/10000000000 : ℝ)|^4803 ≤ (11859633494257/100000000000000 : ℝ)^3779
        have hw : |(-1868440837/10000000000 : ℝ)|=(1868440837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s1_3 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4193543211/10000000000 : ℝ)*x 0 + (29803039/80000000 : ℝ)*x 1 + (117622483/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193543211/10000000000 : ℝ)^4803 ≤ (16568435333157/50000000000000 : ℝ)^3779 := by
    have hnat : (4193543211 : ℕ)^4803*50000000000000^3779 ≤ 16568435333157^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193543211 10000000000 16568435333157 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29803039/80000000 : ℝ)^4803 ≤ (3563527946077/12500000000000 : ℝ)^3779 := by
    have hnat : (29803039 : ℕ)^4803*12500000000000^3779 ≤ 3563527946077^3779*80000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29803039 80000000 3563527946077 12500000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117622483/250000000 : ℝ)^4803 ≤ (19177452873983/50000000000000 : ℝ)^3779 := by
    have hnat : (117622483 : ℕ)^4803*50000000000000^3779 ≤ 19177452873983^3779*250000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117622483 250000000 19177452873983 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193543211/10000000000 : ℝ), (29803039/80000000 : ℝ), (117622483/250000000 : ℝ)] ![(16568435333157/50000000000000 : ℝ), (3563527946077/12500000000000 : ℝ), (19177452873983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193543211/10000000000 : ℝ)|^4803 ≤ (16568435333157/50000000000000 : ℝ)^3779
        have hw : |(4193543211/10000000000 : ℝ)|=(4193543211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(29803039/80000000 : ℝ)|^4803 ≤ (3563527946077/12500000000000 : ℝ)^3779
        have hw : |(29803039/80000000 : ℝ)|=(29803039/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117622483/250000000 : ℝ)|^4803 ≤ (19177452873983/50000000000000 : ℝ)^3779
        have hw : |(117622483/250000000 : ℝ)|=(117622483/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s1_4 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-332704501/2000000000 : ℝ)*x 0 + (5131174193/10000000000 : ℝ)*x 1 + (1103129/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332704501/2000000000 : ℝ)^4803 ≤ (10231750029153/100000000000000 : ℝ)^3779 := by
    have hnat : (332704501 : ℕ)^4803*100000000000000^3779 ≤ 10231750029153^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332704501 2000000000 10231750029153 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131174193/10000000000 : ℝ)^4803 ≤ (42824653550303/100000000000000 : ℝ)^3779 := by
    have hnat : (5131174193 : ℕ)^4803*100000000000000^3779 ≤ 42824653550303^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131174193 10000000000 42824653550303 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103129/2000000 : ℝ)^4803 ≤ (4694359641513/10000000000000 : ℝ)^3779 := by
    have hnat : (1103129 : ℕ)^4803*10000000000000^3779 ≤ 4694359641513^3779*2000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103129 2000000 4694359641513 10000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-332704501/2000000000 : ℝ), (5131174193/10000000000 : ℝ), (1103129/2000000 : ℝ)] ![(10231750029153/100000000000000 : ℝ), (42824653550303/100000000000000 : ℝ), (4694359641513/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-332704501/2000000000 : ℝ)|^4803 ≤ (10231750029153/100000000000000 : ℝ)^3779
        have hw : |(-332704501/2000000000 : ℝ)|=(332704501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131174193/10000000000 : ℝ)|^4803 ≤ (42824653550303/100000000000000 : ℝ)^3779
        have hw : |(5131174193/10000000000 : ℝ)|=(5131174193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103129/2000000 : ℝ)|^4803 ≤ (4694359641513/10000000000000 : ℝ)^3779
        have hw : |(1103129/2000000 : ℝ)|=(1103129/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s1_5 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316009469/2500000000 : ℝ)*x 0 + (-739890097/5000000000 : ℝ)*x 1 + (2757822669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316009469/2500000000 : ℝ)^4803 ≤ (44238917766649/100000000000000 : ℝ)^3779 := by
    have hnat : (1316009469 : ℕ)^4803*100000000000000^3779 ≤ 44238917766649^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316009469 2500000000 44238917766649 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (739890097/5000000000 : ℝ)^4803 ≤ (8817482141239/100000000000000 : ℝ)^3779 := by
    have hnat : (739890097 : ℕ)^4803*100000000000000^3779 ≤ 8817482141239^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739890097 5000000000 8817482141239 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2757822669/5000000000 : ℝ)^4803 ≤ (46943600071351/100000000000000 : ℝ)^3779 := by
    have hnat : (2757822669 : ℕ)^4803*100000000000000^3779 ≤ 46943600071351^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757822669 5000000000 46943600071351 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316009469/2500000000 : ℝ), (-739890097/5000000000 : ℝ), (2757822669/5000000000 : ℝ)] ![(44238917766649/100000000000000 : ℝ), (8817482141239/100000000000000 : ℝ), (46943600071351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316009469/2500000000 : ℝ)|^4803 ≤ (44238917766649/100000000000000 : ℝ)^3779
        have hw : |(1316009469/2500000000 : ℝ)|=(1316009469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-739890097/5000000000 : ℝ)|^4803 ≤ (8817482141239/100000000000000 : ℝ)^3779
        have hw : |(-739890097/5000000000 : ℝ)|=(739890097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2757822669/5000000000 : ℝ)|^4803 ≤ (46943600071351/100000000000000 : ℝ)^3779
        have hw : |(2757822669/5000000000 : ℝ)|=(2757822669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s1_6 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264037227/10000000000 : ℝ)*x 0 + (2757822791/5000000000 : ℝ)*x 1 + (-739890381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264037227/10000000000 : ℝ)^4803 ≤ (11059727708633/25000000000000 : ℝ)^3779 := by
    have hnat : (5264037227 : ℕ)^4803*25000000000000^3779 ≤ 11059727708633^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264037227 10000000000 11059727708633 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757822791/5000000000 : ℝ)^4803 ≤ (46943602710753/100000000000000 : ℝ)^3779 := by
    have hnat : (2757822791 : ℕ)^4803*100000000000000^3779 ≤ 46943602710753^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757822791 5000000000 46943602710753 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (739890381/5000000000 : ℝ)^4803 ≤ (8817486442853/100000000000000 : ℝ)^3779 := by
    have hnat : (739890381 : ℕ)^4803*100000000000000^3779 ≤ 8817486442853^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739890381 5000000000 8817486442853 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264037227/10000000000 : ℝ), (2757822791/5000000000 : ℝ), (-739890381/5000000000 : ℝ)] ![(11059727708633/25000000000000 : ℝ), (46943602710753/100000000000000 : ℝ), (8817486442853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264037227/10000000000 : ℝ)|^4803 ≤ (11059727708633/25000000000000 : ℝ)^3779
        have hw : |(5264037227/10000000000 : ℝ)|=(5264037227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757822791/5000000000 : ℝ)|^4803 ≤ (46943602710753/100000000000000 : ℝ)^3779
        have hw : |(2757822791/5000000000 : ℝ)|=(2757822791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-739890381/5000000000 : ℝ)|^4803 ≤ (8817486442853/100000000000000 : ℝ)^3779
        have hw : |(-739890381/5000000000 : ℝ)|=(739890381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s1_7 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2097021533/5000000000 : ℝ)*x 0 + (146701801/312500000 : ℝ)*x 1 + (1867989897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097021533/5000000000 : ℝ)^4803 ≤ (33141890821229/100000000000000 : ℝ)^3779 := by
    have hnat : (2097021533 : ℕ)^4803*100000000000000^3779 ≤ 33141890821229^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097021533 5000000000 33141890821229 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146701801/312500000 : ℝ)^4803 ≤ (478084385239/1250000000000 : ℝ)^3779 := by
    have hnat : (146701801 : ℕ)^4803*1250000000000^3779 ≤ 478084385239^3779*312500000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146701801 312500000 478084385239 1250000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867989897/5000000000 : ℝ)^4803 ≤ (28611358339023/100000000000000 : ℝ)^3779 := by
    have hnat : (1867989897 : ℕ)^4803*100000000000000^3779 ≤ 28611358339023^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867989897 5000000000 28611358339023 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097021533/5000000000 : ℝ), (146701801/312500000 : ℝ), (1867989897/5000000000 : ℝ)] ![(33141890821229/100000000000000 : ℝ), (478084385239/1250000000000 : ℝ), (28611358339023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097021533/5000000000 : ℝ)|^4803 ≤ (33141890821229/100000000000000 : ℝ)^3779
        have hw : |(2097021533/5000000000 : ℝ)|=(2097021533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(146701801/312500000 : ℝ)|^4803 ≤ (478084385239/1250000000000 : ℝ)^3779
        have hw : |(146701801/312500000 : ℝ)|=(146701801/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1867989897/5000000000 : ℝ)|^4803 ≤ (28611358339023/100000000000000 : ℝ)^3779
        have hw : |(1867989897/5000000000 : ℝ)|=(1867989897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1621_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2999/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2129/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9321/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4413/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2999/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2129/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2999/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2129/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2999/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2129/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2999/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2129/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2999/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2129/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2999/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2129/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2129/50000 : ℝ) ^ (4799/1024 : ℝ) ≤ (301182803147/800000000000000000 : ℝ) := by
    have hpowers : (2129/50000 : ℝ)^4799 ≤ (301182803147/800000000000000000 : ℝ)^1024 := by
      have hnat : (2129 : ℕ)^4799*800000000000000000^1024 ≤ 301182803147^1024*50000^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2129 50000 301182803147 800000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2129/50000 : ℝ)) (X := (301182803147/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2999/12500 : ℝ) ^ (4799/1024 : ℝ) ≤ (124356044934005143/100000000000000000000 : ℝ) := by
    have hpowers : (2999/12500 : ℝ)^4799 ≤ (124356044934005143/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2999 : ℕ)^4799*100000000000000000000^1024 ≤ 124356044934005143^1024*12500^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2999 12500 124356044934005143 100000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2999/12500 : ℝ)) (X := (124356044934005143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (400000301182803147/400000000000000000 : ℝ) ≤ (400000064265701/400000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (400000301182803147/400000000000000000 : ℝ)^1024 ≤ (400000064265701/400000000000000 : ℝ)^4799 := by
      have hnat : (400000301182803147 : ℕ)^1024*400000000000000^4799 ≤ 400000064265701^4799*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400000301182803147 400000000000000000 400000064265701 400000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000064265701/400000000000000 : ℝ)) (X := (400000301182803147/400000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50062196846392199259/50000000000000000000 : ℝ) ≤ (5001326493714923/5000000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (50062196846392199259/50000000000000000000 : ℝ)^1024 ≤ (5001326493714923/5000000000000000 : ℝ)^4799 := by
      have hnat : (50062196846392199259 : ℕ)^1024*5000000000000000^4799 ≤ 5001326493714923^4799*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50062196846392199259 50000000000000000000 5001326493714923 5000000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001326493714923/5000000000000000 : ℝ)) (X := (50062196846392199259/50000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50124356044934005143/50000000000000000000 : ℝ) ≤ (10005304368217167/10000000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (50124356044934005143/50000000000000000000 : ℝ)^1024 ≤ (10005304368217167/10000000000000000 : ℝ)^4799 := by
      have hnat : (50124356044934005143 : ℕ)^1024*10000000000000000^4799 ≤ 10005304368217167^4799*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50124356044934005143 50000000000000000000 10005304368217167 10000000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005304368217167/10000000000000000 : ℝ)) (X := (50124356044934005143/50000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(301182803147/800000000000000000 : ℝ) ≤ ((98658726273349381357/98670000000000000000 : ℝ)+2*(2651380787321/1973400000000000 : ℝ)*(2129/50000 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (98658726273349381357/98670000000000000000 : ℝ)+2*(2651380787321/1973400000000000 : ℝ)*(2129/50000 : ℝ)=(400000064265701/400000000000000 : ℝ) by norm_num, show 1+2*(301182803147/800000000000000000 : ℝ)=(400000301182803147/400000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(124356044934005143/100000000000000000000 : ℝ)+(301182803147/800000000000000000 : ℝ) ≤ ((98658726273349381357/98670000000000000000 : ℝ)+(2651380787321/1973400000000000 : ℝ)*((2999/12500 : ℝ)+(2129/50000 : ℝ)))^(4799/1024 : ℝ) := by
    rw [show (98658726273349381357/98670000000000000000 : ℝ)+(2651380787321/1973400000000000 : ℝ)*((2999/12500 : ℝ)+(2129/50000 : ℝ))=(5001326493714923/5000000000000000 : ℝ) by norm_num, show 1+(124356044934005143/100000000000000000000 : ℝ)+(301182803147/800000000000000000 : ℝ)=(50062196846392199259/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(124356044934005143/100000000000000000000 : ℝ) ≤ ((98658726273349381357/98670000000000000000 : ℝ)+2*(2651380787321/1973400000000000 : ℝ)*(2999/12500 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (98658726273349381357/98670000000000000000 : ℝ)+2*(2651380787321/1973400000000000 : ℝ)*(2999/12500 : ℝ)=(10005304368217167/10000000000000000 : ℝ) by norm_num, show 1+2*(124356044934005143/100000000000000000000 : ℝ)=(50124356044934005143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (98658726273349381357/98670000000000000000 : ℝ)*(X 1 0+X 2 0)+(2651380787321/1973400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (2129/50000 : ℝ)) (hi := (2999/12500 : ℝ)) (c := (98658726273349381357/98670000000000000000 : ℝ)) (alpha := (2651380787321/1973400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (98658726273349381357/98670000000000000000 : ℝ)*(X 0 1+X 2 1)+(2651380787321/1973400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (2129/50000 : ℝ)) (hi := (2999/12500 : ℝ)) (c := (98658726273349381357/98670000000000000000 : ℝ)) (alpha := (2651380787321/1973400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (98658726273349381357/98670000000000000000 : ℝ)*(X 0 2+X 1 2)+(2651380787321/1973400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (2129/50000 : ℝ)) (hi := (2999/12500 : ℝ)) (c := (98658726273349381357/98670000000000000000 : ℝ)) (alpha := (2651380787321/1973400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-415830291/2500000000 : ℝ)*X 0 0+(275994863/500000000 : ℝ)*X 0 1+(5126985319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1342182217/2500000000 : ℝ)*X 1 0+(-116777543/625000000 : ℝ)*X 1 1+(2563492561/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684364547/5000000000 : ℝ)*X 2 0+(5126984779/10000000000 : ℝ)*X 2 1+(-1868440837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4193543211/10000000000 : ℝ)*X 0 0+(29803039/80000000 : ℝ)*X 0 1+(117622483/250000000 : ℝ)*X 0 2+(4193543211/10000000000 : ℝ)*X 1 0+(29803039/80000000 : ℝ)*X 1 1+(117622483/250000000 : ℝ)*X 1 2+(4193543211/10000000000 : ℝ)*X 2 0+(29803039/80000000 : ℝ)*X 2 1+(117622483/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-332704501/2000000000 : ℝ)*X 0 0+(5131174193/10000000000 : ℝ)*X 0 1+(1103129/2000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1316009469/2500000000 : ℝ)*X 1 0+(-739890097/5000000000 : ℝ)*X 1 1+(2757822669/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5264037227/10000000000 : ℝ)*X 2 0+(2757822791/5000000000 : ℝ)*X 2 1+(-739890381/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2097021533/5000000000 : ℝ)*X 0 0+(146701801/312500000 : ℝ)*X 0 1+(1867989897/5000000000 : ℝ)*X 0 2+(2097021533/5000000000 : ℝ)*X 1 0+(146701801/312500000 : ℝ)*X 1 1+(1867989897/5000000000 : ℝ)*X 1 2+(2097021533/5000000000 : ℝ)*X 2 0+(146701801/312500000 : ℝ)*X 2 1+(1867989897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1769709513526793173779/1265000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169115661/100000000000000 : ℝ)*(base1) + (174249187/50000000000000 : ℝ)*(base19) + (665613/125000000000 : ℝ)*(base23) + (8244991/25000000000000 : ℝ)*(upper3) + (41261093/100000000000000 : ℝ)*(lower4) + (29114107/100000000000000 : ℝ)*(upper5) + (891502428665823/50000000000000 : ℝ)*(major0) + (891502428665823/50000000000000 : ℝ)*(major1) + (891502428665823/50000000000000 : ℝ)*(major2) + (1272549848880141/50000000000000 : ℝ)*(sp0) + (1272549590073123/50000000000000 : ℝ)*(sp1) + (127254949807711/5000000000000 : ℝ)*(sp2) + (510454683098837/50000000000000 : ℝ)*(sp3) + (604072667/100000000000000 : ℝ)*(sp7) + (1020910139386003/100000000000000 : ℝ)*(f.failure) + (127254976432231/5000000000000 : ℝ)*(f.sum) + (4055528292877/1265000000000000000000000000 : ℝ)*base65 + (1377746545249245851/126500000000000000000000000000000 : ℝ)*base68 + (482285467567754149/126500000000000000000000000000000 : ℝ)*base69 + (295945761724245851/126500000000000000000000000000000 : ℝ)*base72 + (2808789350493/1265000000000000000000000000 : ℝ)*base74 + (731382682736754149/126500000000000000000000000000000 : ℝ)*base75 + (506295926452245851/126500000000000000000000000000000 : ℝ)*base78 + (301162712160754149/126500000000000000000000000000000 : ℝ)*base79 + (8886525153127/1265000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1351321/125000000000000000000 : ℝ)*base89 + (1351321/125000000000000000000 : ℝ)*base91 + (1351321/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1418348352599876705513611139/822250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68002387/12500000000000 : ℝ)*(base19) + (325411853/100000000000000 : ℝ)*(base23) + (9037173/12500000000000 : ℝ)*(upper2) + (123823043/100000000000000 : ℝ)*(upper3) + (1822148219973527/100000000000000 : ℝ)*(major0) + (1822148219973527/100000000000000 : ℝ)*(major1) + (1822148219973527/100000000000000 : ℝ)*(major2) + (5352935869/100000000000000 : ℝ)*(sp1) + (178956199/5000000000000 : ℝ)*(sp2) + (846443203/100000000000000 : ℝ)*(sp3) + (1300486798775971/50000000000000 : ℝ)*(sp4) + (162560481287311/6250000000000 : ℝ)*(sp5) + (2600969693016109/100000000000000 : ℝ)*(sp6) + (260830484613309/25000000000000 : ℝ)*(sp7) + (521661392448219/50000000000000 : ℝ)*(f.failure) + (1300486798775971/50000000000000 : ℝ)*(f.sum) + (45839585110837/98670000000000000000000000000 : ℝ)*base65 + (63665047356535313861/9867000000000000000000000000000000 : ℝ)*base68 + (29572152450322313861/9867000000000000000000000000000000 : ℝ)*base70 + (10675238593966686139/9867000000000000000000000000000000 : ℝ)*base71 + (410149400452703/98670000000000000000000000000 : ℝ)*base74 + (17157975605824313861/9867000000000000000000000000000000 : ℝ)*base76 + (30941148654898313861/9867000000000000000000000000000000 : ℝ)*base78 + (90376477185619313861/9867000000000000000000000000000000 : ℝ)*base80 + (6023076544253/98670000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (338567/62500000000000000000 : ℝ)*base90 + (338567/62500000000000000000 : ℝ)*base92 + (338567/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1621_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2999/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2129/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9321/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4413/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1621_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1621_s2_0 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-837893501/5000000000 : ℝ)*x 0 + (5462116637/10000000000 : ℝ)*x 1 + (5176587159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837893501/5000000000 : ℝ)^4803 ≤ (5163860456583/50000000000000 : ℝ)^3779 := by
    have hnat : (837893501 : ℕ)^4803*50000000000000^3779 ≤ 5163860456583^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837893501 5000000000 5163860456583 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462116637/10000000000 : ℝ)^4803 ≤ (11591332842459/25000000000000 : ℝ)^3779 := by
    have hnat : (5462116637 : ℕ)^4803*25000000000000^3779 ≤ 11591332842459^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462116637 10000000000 11591332842459 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176587159/10000000000 : ℝ)^4803 ≤ (1353342115803/3125000000000 : ℝ)^3779 := by
    have hnat : (5176587159 : ℕ)^4803*3125000000000^3779 ≤ 1353342115803^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176587159 10000000000 1353342115803 3125000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-837893501/5000000000 : ℝ), (5462116637/10000000000 : ℝ), (5176587159/10000000000 : ℝ)] ![(5163860456583/50000000000000 : ℝ), (11591332842459/25000000000000 : ℝ), (1353342115803/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-837893501/5000000000 : ℝ)|^4803 ≤ (5163860456583/50000000000000 : ℝ)^3779
        have hw : |(-837893501/5000000000 : ℝ)|=(837893501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462116637/10000000000 : ℝ)|^4803 ≤ (11591332842459/25000000000000 : ℝ)^3779
        have hw : |(5462116637/10000000000 : ℝ)|=(5462116637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176587159/10000000000 : ℝ)|^4803 ≤ (1353342115803/3125000000000 : ℝ)^3779
        have hw : |(5176587159/10000000000 : ℝ)|=(5176587159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s2_1 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353601253/10000000000 : ℝ)*x 0 + (-1823128171/10000000000 : ℝ)*x 1 + (161768349/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353601253/10000000000 : ℝ)^4803 ≤ (22598880401099/50000000000000 : ℝ)^3779 := by
    have hnat : (5353601253 : ℕ)^4803*50000000000000^3779 ≤ 22598880401099^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353601253 10000000000 22598880401099 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1823128171/10000000000 : ℝ)^4803 ≤ (2299058276533/20000000000000 : ℝ)^3779 := by
    have hnat : (1823128171 : ℕ)^4803*20000000000000^3779 ≤ 2299058276533^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823128171 10000000000 2299058276533 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161768349/312500000 : ℝ)^4803 ≤ (2706684237587/6250000000000 : ℝ)^3779 := by
    have hnat : (161768349 : ℕ)^4803*6250000000000^3779 ≤ 2706684237587^3779*312500000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161768349 312500000 2706684237587 6250000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353601253/10000000000 : ℝ), (-1823128171/10000000000 : ℝ), (161768349/312500000 : ℝ)] ![(22598880401099/50000000000000 : ℝ), (2299058276533/20000000000000 : ℝ), (2706684237587/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353601253/10000000000 : ℝ)|^4803 ≤ (22598880401099/50000000000000 : ℝ)^3779
        have hw : |(5353601253/10000000000 : ℝ)|=(5353601253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1823128171/10000000000 : ℝ)|^4803 ≤ (2299058276533/20000000000000 : ℝ)^3779
        have hw : |(-1823128171/10000000000 : ℝ)|=(1823128171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161768349/312500000 : ℝ)|^4803 ≤ (2706684237587/6250000000000 : ℝ)^3779
        have hw : |(161768349/312500000 : ℝ)|=(161768349/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s2_2 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676800637/5000000000 : ℝ)*x 0 + (517658713/1000000000 : ℝ)*x 1 + (-911564097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676800637/5000000000 : ℝ)^4803 ≤ (11299440256883/25000000000000 : ℝ)^3779 := by
    have hnat : (2676800637 : ℕ)^4803*25000000000000^3779 ≤ 11299440256883^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676800637 5000000000 11299440256883 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517658713/1000000000 : ℝ)^4803 ≤ (1353342106167/3125000000000 : ℝ)^3779 := by
    have hnat : (517658713 : ℕ)^4803*3125000000000^3779 ≤ 1353342106167^3779*1000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517658713 1000000000 1353342106167 3125000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (911564097/5000000000 : ℝ)^4803 ≤ (11495291566983/100000000000000 : ℝ)^3779 := by
    have hnat : (911564097 : ℕ)^4803*100000000000000^3779 ≤ 11495291566983^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911564097 5000000000 11495291566983 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676800637/5000000000 : ℝ), (517658713/1000000000 : ℝ), (-911564097/5000000000 : ℝ)] ![(11299440256883/25000000000000 : ℝ), (1353342106167/3125000000000 : ℝ), (11495291566983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676800637/5000000000 : ℝ)|^4803 ≤ (11299440256883/25000000000000 : ℝ)^3779
        have hw : |(2676800637/5000000000 : ℝ)|=(2676800637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517658713/1000000000 : ℝ)|^4803 ≤ (1353342106167/3125000000000 : ℝ)^3779
        have hw : |(517658713/1000000000 : ℝ)|=(517658713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-911564097/5000000000 : ℝ)|^4803 ≤ (11495291566983/100000000000000 : ℝ)^3779
        have hw : |(-911564097/5000000000 : ℝ)|=(911564097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s2_3 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525346079/1250000000 : ℝ)*x 0 + (3858269061/10000000000 : ℝ)*x 1 + (4570085923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525346079/1250000000 : ℝ)^4803 ≤ (16614774862591/50000000000000 : ℝ)^3779 := by
    have hnat : (525346079 : ℕ)^4803*50000000000000^3779 ≤ 16614774862591^3779*1250000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525346079 1250000000 16614774862591 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3858269061/10000000000 : ℝ)^4803 ≤ (5961380001471/20000000000000 : ℝ)^3779 := by
    have hnat : (3858269061 : ℕ)^4803*20000000000000^3779 ≤ 5961380001471^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3858269061 10000000000 5961380001471 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4570085923/10000000000 : ℝ)^4803 ≤ (18481775127217/50000000000000 : ℝ)^3779 := by
    have hnat : (4570085923 : ℕ)^4803*50000000000000^3779 ≤ 18481775127217^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570085923 10000000000 18481775127217 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525346079/1250000000 : ℝ), (3858269061/10000000000 : ℝ), (4570085923/10000000000 : ℝ)] ![(16614774862591/50000000000000 : ℝ), (5961380001471/20000000000000 : ℝ), (18481775127217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525346079/1250000000 : ℝ)|^4803 ≤ (16614774862591/50000000000000 : ℝ)^3779
        have hw : |(525346079/1250000000 : ℝ)|=(525346079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3858269061/10000000000 : ℝ)|^4803 ≤ (5961380001471/20000000000000 : ℝ)^3779
        have hw : |(3858269061/10000000000 : ℝ)|=(3858269061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4570085923/10000000000 : ℝ)|^4803 ≤ (18481775127217/50000000000000 : ℝ)^3779
        have hw : |(4570085923/10000000000 : ℝ)|=(4570085923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s2_4 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418966001/2500000000 : ℝ)*x 0 + (5178805917/10000000000 : ℝ)*x 1 + (5459873767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418966001/2500000000 : ℝ)^4803 ≤ (2582081016051/25000000000000 : ℝ)^3779 := by
    have hnat : (418966001 : ℕ)^4803*25000000000000^3779 ≤ 2582081016051^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418966001 2500000000 2582081016051 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178805917/10000000000 : ℝ)^4803 ≤ (1354079399981/3125000000000 : ℝ)^3779 := by
    have hnat : (5178805917 : ℕ)^4803*3125000000000^3779 ≤ 1354079399981^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178805917 10000000000 1354079399981 3125000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459873767/10000000000 : ℝ)^4803 ≤ (2896320945103/6250000000000 : ℝ)^3779 := by
    have hnat : (5459873767 : ℕ)^4803*6250000000000^3779 ≤ 2896320945103^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459873767 10000000000 2896320945103 6250000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418966001/2500000000 : ℝ), (5178805917/10000000000 : ℝ), (5459873767/10000000000 : ℝ)] ![(2582081016051/25000000000000 : ℝ), (1354079399981/3125000000000 : ℝ), (2896320945103/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418966001/2500000000 : ℝ)|^4803 ≤ (2582081016051/25000000000000 : ℝ)^3779
        have hw : |(-418966001/2500000000 : ℝ)|=(418966001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178805917/10000000000 : ℝ)|^4803 ≤ (1354079399981/3125000000000 : ℝ)^3779
        have hw : |(5178805917/10000000000 : ℝ)|=(5178805917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459873767/10000000000 : ℝ)|^4803 ≤ (2896320945103/6250000000000 : ℝ)^3779
        have hw : |(5459873767/10000000000 : ℝ)|=(5459873767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s2_5 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527762051/1000000000 : ℝ)*x 0 + (-1539842043/10000000000 : ℝ)*x 1 + (1091974637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527762051/1000000000 : ℝ)^4803 ≤ (44384047662879/100000000000000 : ℝ)^3779 := by
    have hnat : (527762051 : ℕ)^4803*100000000000000^3779 ≤ 44384047662879^3779*1000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527762051 1000000000 44384047662879 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1539842043/10000000000 : ℝ)^4803 ≤ (9274823468197/100000000000000 : ℝ)^3779 := by
    have hnat : (1539842043 : ℕ)^4803*100000000000000^3779 ≤ 9274823468197^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1539842043 10000000000 9274823468197 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091974637/2000000000 : ℝ)^4803 ≤ (23170564421669/50000000000000 : ℝ)^3779 := by
    have hnat : (1091974637 : ℕ)^4803*50000000000000^3779 ≤ 23170564421669^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091974637 2000000000 23170564421669 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527762051/1000000000 : ℝ), (-1539842043/10000000000 : ℝ), (1091974637/2000000000 : ℝ)] ![(44384047662879/100000000000000 : ℝ), (9274823468197/100000000000000 : ℝ), (23170564421669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527762051/1000000000 : ℝ)|^4803 ≤ (44384047662879/100000000000000 : ℝ)^3779
        have hw : |(527762051/1000000000 : ℝ)|=(527762051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1539842043/10000000000 : ℝ)|^4803 ≤ (9274823468197/100000000000000 : ℝ)^3779
        have hw : |(-1539842043/10000000000 : ℝ)|=(1539842043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091974637/2000000000 : ℝ)|^4803 ≤ (23170564421669/50000000000000 : ℝ)^3779
        have hw : |(1091974637/2000000000 : ℝ)|=(1091974637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s2_6 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055524043/2000000000 : ℝ)*x 0 + (5459873761/10000000000 : ℝ)*x 1 + (-307968329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055524043/2000000000 : ℝ)^4803 ≤ (8876808901943/20000000000000 : ℝ)^3779 := by
    have hnat : (1055524043 : ℕ)^4803*20000000000000^3779 ≤ 8876808901943^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055524043 2000000000 8876808901943 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459873761/10000000000 : ℝ)^4803 ≤ (46341135056923/100000000000000 : ℝ)^3779 := by
    have hnat : (5459873761 : ℕ)^4803*100000000000000^3779 ≤ 46341135056923^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459873761 10000000000 46341135056923 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307968329/2000000000 : ℝ)^4803 ≤ (9274820421367/100000000000000 : ℝ)^3779 := by
    have hnat : (307968329 : ℕ)^4803*100000000000000^3779 ≤ 9274820421367^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307968329 2000000000 9274820421367 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055524043/2000000000 : ℝ), (5459873761/10000000000 : ℝ), (-307968329/2000000000 : ℝ)] ![(8876808901943/20000000000000 : ℝ), (46341135056923/100000000000000 : ℝ), (9274820421367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055524043/2000000000 : ℝ)|^4803 ≤ (8876808901943/20000000000000 : ℝ)^3779
        have hw : |(1055524043/2000000000 : ℝ)|=(1055524043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459873761/10000000000 : ℝ)|^4803 ≤ (46341135056923/100000000000000 : ℝ)^3779
        have hw : |(5459873761/10000000000 : ℝ)|=(5459873761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-307968329/2000000000 : ℝ)|^4803 ≤ (9274820421367/100000000000000 : ℝ)^3779
        have hw : |(-307968329/2000000000 : ℝ)|=(307968329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s2_7 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84059231/200000000 : ℝ)*x 0 + (1141138401/2500000000 : ℝ)*x 1 + (3863861619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84059231/200000000 : ℝ)^4803 ≤ (33231488378357/100000000000000 : ℝ)^3779 := by
    have hnat : (84059231 : ℕ)^4803*100000000000000^3779 ≤ 33231488378357^3779*200000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84059231 200000000 33231488378357 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141138401/2500000000 : ℝ)^4803 ≤ (36906688407167/100000000000000 : ℝ)^3779 := by
    have hnat : (1141138401 : ℕ)^4803*100000000000000^3779 ≤ 36906688407167^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141138401 2500000000 36906688407167 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3863861619/10000000000 : ℝ)^4803 ≤ (14930911597999/50000000000000 : ℝ)^3779 := by
    have hnat : (3863861619 : ℕ)^4803*50000000000000^3779 ≤ 14930911597999^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3863861619 10000000000 14930911597999 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84059231/200000000 : ℝ), (1141138401/2500000000 : ℝ), (3863861619/10000000000 : ℝ)] ![(33231488378357/100000000000000 : ℝ), (36906688407167/100000000000000 : ℝ), (14930911597999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84059231/200000000 : ℝ)|^4803 ≤ (33231488378357/100000000000000 : ℝ)^3779
        have hw : |(84059231/200000000 : ℝ)|=(84059231/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1141138401/2500000000 : ℝ)|^4803 ≤ (36906688407167/100000000000000 : ℝ)^3779
        have hw : |(1141138401/2500000000 : ℝ)|=(1141138401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3863861619/10000000000 : ℝ)|^4803 ≤ (14930911597999/50000000000000 : ℝ)^3779
        have hw : |(3863861619/10000000000 : ℝ)|=(3863861619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1621_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4413/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1299/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16449/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4413/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4413/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4413/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4413/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4413/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4413/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9321/100000 : ℝ) ^ (4799/1024 : ℝ) ≤ (59213656734291/4000000000000000000 : ℝ) := by
    have hpowers : (9321/100000 : ℝ)^4799 ≤ (59213656734291/4000000000000000000 : ℝ)^1024 := by
      have hnat : (9321 : ℕ)^4799*4000000000000000000^1024 ≤ 59213656734291^1024*100000^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9321 100000 59213656734291 4000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9321/100000 : ℝ)) (X := (59213656734291/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4413/25000 : ℝ) ^ (4799/1024 : ℝ) ≤ (14758834114304963/50000000000000000000 : ℝ) := by
    have hpowers : (4413/25000 : ℝ)^4799 ≤ (14758834114304963/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4413 : ℕ)^4799*50000000000000000000^1024 ≤ 14758834114304963^1024*25000^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4413 25000 14758834114304963 50000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4413/25000 : ℝ)) (X := (14758834114304963/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000059213656734291/2000000000000000000 : ℝ) ≤ (10000063173659549/10000000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (2000059213656734291/2000000000000000000 : ℝ)^1024 ≤ (10000063173659549/10000000000000000 : ℝ)^4799 := by
      have hnat : (2000059213656734291 : ℕ)^1024*10000000000000000^4799 ≤ 10000063173659549^4799*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000059213656734291 2000000000000000000 10000063173659549 10000000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000063173659549/10000000000000000 : ℝ)) (X := (2000059213656734291/2000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030998009646967201/100000000000000000000 : ℝ) ≤ (400026453921781/400000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (100030998009646967201/100000000000000000000 : ℝ)^1024 ≤ (400026453921781/400000000000000 : ℝ)^4799 := by
      have hnat : (100030998009646967201 : ℕ)^1024*400000000000000^4799 ≤ 400026453921781^4799*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030998009646967201 100000000000000000000 400026453921781 400000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400026453921781/400000000000000 : ℝ)) (X := (100030998009646967201/100000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014758834114304963/25000000000000000000 : ℝ) ≤ (10001259522429501/10000000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (25014758834114304963/25000000000000000000 : ℝ)^1024 ≤ (10001259522429501/10000000000000000 : ℝ)^4799 := by
      have hnat : (25014758834114304963 : ℕ)^1024*10000000000000000^4799 ≤ 10001259522429501^4799*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014758834114304963 25000000000000000000 10001259522429501 10000000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001259522429501/10000000000000000 : ℝ)) (X := (25014758834114304963/25000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(59213656734291/4000000000000000000 : ℝ) ≤ ((27766458377624326709/27770000000000000000 : ℝ)+2*(37385899061/52068750000000 : ℝ)*(9321/100000 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (27766458377624326709/27770000000000000000 : ℝ)+2*(37385899061/52068750000000 : ℝ)*(9321/100000 : ℝ)=(10000063173659549/10000000000000000 : ℝ) by norm_num, show 1+2*(59213656734291/4000000000000000000 : ℝ)=(2000059213656734291/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14758834114304963/50000000000000000000 : ℝ)+(59213656734291/4000000000000000000 : ℝ) ≤ ((27766458377624326709/27770000000000000000 : ℝ)+(37385899061/52068750000000 : ℝ)*((4413/25000 : ℝ)+(9321/100000 : ℝ)))^(4799/1024 : ℝ) := by
    rw [show (27766458377624326709/27770000000000000000 : ℝ)+(37385899061/52068750000000 : ℝ)*((4413/25000 : ℝ)+(9321/100000 : ℝ))=(400026453921781/400000000000000 : ℝ) by norm_num, show 1+(14758834114304963/50000000000000000000 : ℝ)+(59213656734291/4000000000000000000 : ℝ)=(100030998009646967201/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14758834114304963/50000000000000000000 : ℝ) ≤ ((27766458377624326709/27770000000000000000 : ℝ)+2*(37385899061/52068750000000 : ℝ)*(4413/25000 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (27766458377624326709/27770000000000000000 : ℝ)+2*(37385899061/52068750000000 : ℝ)*(4413/25000 : ℝ)=(10001259522429501/10000000000000000 : ℝ) by norm_num, show 1+2*(14758834114304963/50000000000000000000 : ℝ)=(25014758834114304963/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27766458377624326709/27770000000000000000 : ℝ)*(X 1 0+X 2 0)+(37385899061/52068750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (9321/100000 : ℝ)) (hi := (4413/25000 : ℝ)) (c := (27766458377624326709/27770000000000000000 : ℝ)) (alpha := (37385899061/52068750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27766458377624326709/27770000000000000000 : ℝ)*(X 0 1+X 2 1)+(37385899061/52068750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (9321/100000 : ℝ)) (hi := (4413/25000 : ℝ)) (c := (27766458377624326709/27770000000000000000 : ℝ)) (alpha := (37385899061/52068750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27766458377624326709/27770000000000000000 : ℝ)*(X 0 2+X 1 2)+(37385899061/52068750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (9321/100000 : ℝ)) (hi := (4413/25000 : ℝ)) (c := (27766458377624326709/27770000000000000000 : ℝ)) (alpha := (37385899061/52068750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-837893501/5000000000 : ℝ)*X 0 0+(5462116637/10000000000 : ℝ)*X 0 1+(5176587159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353601253/10000000000 : ℝ)*X 1 0+(-1823128171/10000000000 : ℝ)*X 1 1+(161768349/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676800637/5000000000 : ℝ)*X 2 0+(517658713/1000000000 : ℝ)*X 2 1+(-911564097/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((525346079/1250000000 : ℝ)*X 0 0+(3858269061/10000000000 : ℝ)*X 0 1+(4570085923/10000000000 : ℝ)*X 0 2+(525346079/1250000000 : ℝ)*X 1 0+(3858269061/10000000000 : ℝ)*X 1 1+(4570085923/10000000000 : ℝ)*X 1 2+(525346079/1250000000 : ℝ)*X 2 0+(3858269061/10000000000 : ℝ)*X 2 1+(4570085923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-418966001/2500000000 : ℝ)*X 0 0+(5178805917/10000000000 : ℝ)*X 0 1+(5459873767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((527762051/1000000000 : ℝ)*X 1 0+(-1539842043/10000000000 : ℝ)*X 1 1+(1091974637/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055524043/2000000000 : ℝ)*X 2 0+(5459873761/10000000000 : ℝ)*X 2 1+(-307968329/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((84059231/200000000 : ℝ)*X 0 0+(1141138401/2500000000 : ℝ)*X 0 1+(3863861619/10000000000 : ℝ)*X 0 2+(84059231/200000000 : ℝ)*X 1 0+(1141138401/2500000000 : ℝ)*X 1 1+(3863861619/10000000000 : ℝ)*X 1 2+(84059231/200000000 : ℝ)*X 2 0+(1141138401/2500000000 : ℝ)*X 2 1+(3863861619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9583184599051923417087/3471250000000000000000000000 : ℝ) := by norm_num
    linear_combination (217088597/50000000000000 : ℝ)*(base19) + (417646363/100000000000000 : ℝ)*(base23) + (648189/4000000000000 : ℝ)*(lower2) + (78146323/100000000000000 : ℝ)*(upper3) + (40694631/100000000000000 : ℝ)*(upper5) + (1226783850055929/50000000000000 : ℝ)*(major0) + (1226783850055929/50000000000000 : ℝ)*(major1) + (1226783850055929/50000000000000 : ℝ)*(major2) + (10944595616323/312500000000 : ℝ)*(sp0) + (1751137454160999/50000000000000 : ℝ)*(sp1) + (350227492485283/10000000000000 : ℝ)*(sp2) + (351214411577189/25000000000000 : ℝ)*(sp3) + (593159479/12500000000000 : ℝ)*(sp4) + (36240491/1562500000000 : ℝ)*(sp7) + (70242998285009/5000000000000 : ℝ)*(f.failure) + (437784417812399/12500000000000 : ℝ)*(f.sum) + (1920410823197/433906250000000000000000000 : ℝ)*base66 + (5468499577550692339/1388500000000000000000000000000000 : ℝ)*base68 + (11502577534397307661/1388500000000000000000000000000000 : ℝ)*base69 + (3238750584564307661/1388500000000000000000000000000000 : ℝ)*base71 + (1877108908577/6942500000000000000000000000 : ℝ)*base74 + (8014404107617307661/1388500000000000000000000000000000 : ℝ)*base75 + (5550790329686692339/1388500000000000000000000000000000 : ℝ)*base78 + (5055198162136692339/1388500000000000000000000000000000 : ℝ)*base80 + (2085352110153/433906250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (17963/6250000000000000000 : ℝ)*base89 + (17963/6250000000000000000 : ℝ)*base91 + (17963/6250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5766927862414986799556980463/694250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113038657/10000000000000 : ℝ)*(base19) + (670510571/50000000000000 : ℝ)*(base23) + (28734131/100000000000000 : ℝ)*(upper3) + (11460901/6250000000000 : ℝ)*(lower4) + (287780901/100000000000000 : ℝ)*(upper5) + (1246255145164277/50000000000000 : ℝ)*(major0) + (1246255145164277/50000000000000 : ℝ)*(major1) + (1246255145164277/50000000000000 : ℝ)*(major2) + (612031843/6250000000000 : ℝ)*(sp1) + (14102414851/100000000000000 : ℝ)*(sp2) + (889465662629597/25000000000000 : ℝ)*(sp4) + (355785172762233/10000000000000 : ℝ)*(sp5) + (711569441416479/20000000000000 : ℝ)*(sp6) + (713578826624323/50000000000000 : ℝ)*(sp7) + (713578826624323/50000000000000 : ℝ)*(f.failure) + (889465662629597/25000000000000 : ℝ)*(f.sum) + (52196219555441/10413750000000000000000000000 : ℝ)*base65 + (27887581540516523179/4165500000000000000000000000000000 : ℝ)*base67 + (11284217242921523179/4165500000000000000000000000000000 : ℝ)*base69 + (41288761142614523179/4165500000000000000000000000000000 : ℝ)*base71 + (11240961926963/20827500000000000000000000000 : ℝ)*base74 + (28442147351932523179/4165500000000000000000000000000000 : ℝ)*base75 + (22545850898172023179/4165500000000000000000000000000000 : ℝ)*base77 + (25632782107017023179/4165500000000000000000000000000000 : ℝ)*base79 + (146505935501429/41655000000000000000000000000 : ℝ)*base81 + (338439/62500000000000000000 : ℝ)*base90 + (338439/62500000000000000000 : ℝ)*base92 + (338439/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1621_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4413/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1299/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1621_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1621_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1299/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1621_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1621_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1621_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1299/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1621_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
