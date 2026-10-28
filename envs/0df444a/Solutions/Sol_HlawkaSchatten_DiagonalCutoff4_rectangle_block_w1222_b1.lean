-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1222_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:11:30.833788+00:00
-- url     : https://prove2.me/submissions/0c068bfb-d223-42b8-94c1-3ddbc720592b

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
theorem support_rectangle_w1222_s3_0 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-212619089/1000000000 : ℝ)*x 0 + (5421441897/10000000000 : ℝ)*x 1 + (523904519/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212619089/1000000000 : ℝ)^8415 ≤ (201901615267/1562500000000 : ℝ)^6367 := by
    have hnat : (212619089 : ℕ)^8415*1562500000000^6367 ≤ 201901615267^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212619089 1000000000 201901615267 1562500000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421441897/10000000000 : ℝ)^8415 ≤ (44523629664983/100000000000000 : ℝ)^6367 := by
    have hnat : (5421441897 : ℕ)^8415*100000000000000^6367 ≤ 44523629664983^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421441897 10000000000 44523629664983 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523904519/1000000000 : ℝ)^8415 ≤ (2127733347387/5000000000000 : ℝ)^6367 := by
    have hnat : (523904519 : ℕ)^8415*5000000000000^6367 ≤ 2127733347387^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523904519 1000000000 2127733347387 5000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212619089/1000000000 : ℝ), (5421441897/10000000000 : ℝ), (523904519/1000000000 : ℝ)] ![(201901615267/1562500000000 : ℝ), (44523629664983/100000000000000 : ℝ), (2127733347387/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212619089/1000000000 : ℝ)|^8415 ≤ (201901615267/1562500000000 : ℝ)^6367
        have hw : |(-212619089/1000000000 : ℝ)|=(212619089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421441897/10000000000 : ℝ)|^8415 ≤ (44523629664983/100000000000000 : ℝ)^6367
        have hw : |(5421441897/10000000000 : ℝ)|=(5421441897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523904519/1000000000 : ℝ)|^8415 ≤ (2127733347387/5000000000000 : ℝ)^6367
        have hw : |(523904519/1000000000 : ℝ)|=(523904519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s3_1 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070387027/2000000000 : ℝ)*x 0 + (-2219273247/10000000000 : ℝ)*x 1 + (2619522699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070387027/2000000000 : ℝ)^8415 ≤ (43770754363889/100000000000000 : ℝ)^6367 := by
    have hnat : (1070387027 : ℕ)^8415*100000000000000^6367 ≤ 43770754363889^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070387027 2000000000 43770754363889 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219273247/10000000000 : ℝ)^8415 ≤ (6837288221849/50000000000000 : ℝ)^6367 := by
    have hnat : (2219273247 : ℕ)^8415*50000000000000^6367 ≤ 6837288221849^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219273247 10000000000 6837288221849 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619522699/5000000000 : ℝ)^8415 ≤ (42554669180683/100000000000000 : ℝ)^6367 := by
    have hnat : (2619522699 : ℕ)^8415*100000000000000^6367 ≤ 42554669180683^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619522699 5000000000 42554669180683 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070387027/2000000000 : ℝ), (-2219273247/10000000000 : ℝ), (2619522699/5000000000 : ℝ)] ![(43770754363889/100000000000000 : ℝ), (6837288221849/50000000000000 : ℝ), (42554669180683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070387027/2000000000 : ℝ)|^8415 ≤ (43770754363889/100000000000000 : ℝ)^6367
        have hw : |(1070387027/2000000000 : ℝ)|=(1070387027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2219273247/10000000000 : ℝ)|^8415 ≤ (6837288221849/50000000000000 : ℝ)^6367
        have hw : |(-2219273247/10000000000 : ℝ)|=(2219273247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619522699/5000000000 : ℝ)|^8415 ≤ (42554669180683/100000000000000 : ℝ)^6367
        have hw : |(2619522699/5000000000 : ℝ)|=(2619522699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s3_2 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351934999/10000000000 : ℝ)*x 0 + (5239045791/10000000000 : ℝ)*x 1 + (-2219272909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351934999/10000000000 : ℝ)^8415 ≤ (43770752893841/100000000000000 : ℝ)^6367 := by
    have hnat : (5351934999 : ℕ)^8415*100000000000000^6367 ≤ 43770752893841^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351934999 10000000000 43770752893841 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239045791/10000000000 : ℝ)^8415 ≤ (42554673399657/100000000000000 : ℝ)^6367 := by
    have hnat : (5239045791 : ℕ)^8415*100000000000000^6367 ≤ 42554673399657^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239045791 10000000000 42554673399657 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219272909/10000000000 : ℝ)^8415 ≤ (3418643422781/25000000000000 : ℝ)^6367 := by
    have hnat : (2219272909 : ℕ)^8415*25000000000000^6367 ≤ 3418643422781^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219272909 10000000000 3418643422781 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351934999/10000000000 : ℝ), (5239045791/10000000000 : ℝ), (-2219272909/10000000000 : ℝ)] ![(43770752893841/100000000000000 : ℝ), (42554673399657/100000000000000 : ℝ), (3418643422781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351934999/10000000000 : ℝ)|^8415 ≤ (43770752893841/100000000000000 : ℝ)^6367
        have hw : |(5351934999/10000000000 : ℝ)|=(5351934999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239045791/10000000000 : ℝ)|^8415 ≤ (42554673399657/100000000000000 : ℝ)^6367
        have hw : |(5239045791/10000000000 : ℝ)|=(5239045791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2219272909/10000000000 : ℝ)|^8415 ≤ (3418643422781/25000000000000 : ℝ)^6367
        have hw : |(-2219272909/10000000000 : ℝ)|=(2219272909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s3_3 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175862531/5000000000 : ℝ)*x 0 + (4171244831/10000000000 : ℝ)*x 1 + (907963993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175862531/5000000000 : ℝ)^8415 ≤ (33299201101063/100000000000000 : ℝ)^6367 := by
    have hnat : (2175862531 : ℕ)^8415*100000000000000^6367 ≤ 33299201101063^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175862531 5000000000 33299201101063 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171244831/10000000000 : ℝ)^8415 ≤ (6297249290499/20000000000000 : ℝ)^6367 := by
    have hnat : (4171244831 : ℕ)^8415*20000000000000^6367 ≤ 6297249290499^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171244831 10000000000 6297249290499 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (907963993/2000000000 : ℝ)^8415 ≤ (17607276214399/50000000000000 : ℝ)^6367 := by
    have hnat : (907963993 : ℕ)^8415*50000000000000^6367 ≤ 17607276214399^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907963993 2000000000 17607276214399 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175862531/5000000000 : ℝ), (4171244831/10000000000 : ℝ), (907963993/2000000000 : ℝ)] ![(33299201101063/100000000000000 : ℝ), (6297249290499/20000000000000 : ℝ), (17607276214399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175862531/5000000000 : ℝ)|^8415 ≤ (33299201101063/100000000000000 : ℝ)^6367
        have hw : |(2175862531/5000000000 : ℝ)|=(2175862531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171244831/10000000000 : ℝ)|^8415 ≤ (6297249290499/20000000000000 : ℝ)^6367
        have hw : |(4171244831/10000000000 : ℝ)|=(4171244831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(907963993/2000000000 : ℝ)|^8415 ≤ (17607276214399/50000000000000 : ℝ)^6367
        have hw : |(907963993/2000000000 : ℝ)|=(907963993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s3_4 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-531551443/2500000000 : ℝ)*x 0 + (5239716339/10000000000 : ℝ)*x 1 + (1084153411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531551443/2500000000 : ℝ)^8415 ≤ (12921822913049/100000000000000 : ℝ)^6367 := by
    have hnat : (531551443 : ℕ)^8415*100000000000000^6367 ≤ 12921822913049^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531551443 2500000000 12921822913049 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239716339/10000000000 : ℝ)^8415 ≤ (42561872084303/100000000000000 : ℝ)^6367 := by
    have hnat : (5239716339 : ℕ)^8415*100000000000000^6367 ≤ 42561872084303^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239716339 10000000000 42561872084303 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084153411/2000000000 : ℝ)^8415 ≤ (44516304988733/100000000000000 : ℝ)^6367 := by
    have hnat : (1084153411 : ℕ)^8415*100000000000000^6367 ≤ 44516304988733^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084153411 2000000000 44516304988733 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531551443/2500000000 : ℝ), (5239716339/10000000000 : ℝ), (1084153411/2000000000 : ℝ)] ![(12921822913049/100000000000000 : ℝ), (42561872084303/100000000000000 : ℝ), (44516304988733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531551443/2500000000 : ℝ)|^8415 ≤ (12921822913049/100000000000000 : ℝ)^6367
        have hw : |(-531551443/2500000000 : ℝ)|=(531551443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239716339/10000000000 : ℝ)|^8415 ≤ (42561872084303/100000000000000 : ℝ)^6367
        have hw : |(5239716339/10000000000 : ℝ)|=(5239716339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084153411/2000000000 : ℝ)|^8415 ≤ (44516304988733/100000000000000 : ℝ)^6367
        have hw : |(1084153411/2000000000 : ℝ)|=(1084153411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s3_5 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305464537/10000000000 : ℝ)*x 0 + (-2037551547/10000000000 : ℝ)*x 1 + (1084153343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305464537/10000000000 : ℝ)^8415 ≤ (21634574240781/50000000000000 : ℝ)^6367 := by
    have hnat : (5305464537 : ℕ)^8415*50000000000000^6367 ≤ 21634574240781^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305464537 10000000000 21634574240781 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2037551547/10000000000 : ℝ)^8415 ≤ (488582008029/4000000000000 : ℝ)^6367 := by
    have hnat : (2037551547 : ℕ)^8415*4000000000000^6367 ≤ 488582008029^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037551547 10000000000 488582008029 4000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084153343/2000000000 : ℝ)^8415 ≤ (44516301298477/100000000000000 : ℝ)^6367 := by
    have hnat : (1084153343 : ℕ)^8415*100000000000000^6367 ≤ 44516301298477^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084153343 2000000000 44516301298477 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305464537/10000000000 : ℝ), (-2037551547/10000000000 : ℝ), (1084153343/2000000000 : ℝ)] ![(21634574240781/50000000000000 : ℝ), (488582008029/4000000000000 : ℝ), (44516301298477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305464537/10000000000 : ℝ)|^8415 ≤ (21634574240781/50000000000000 : ℝ)^6367
        have hw : |(5305464537/10000000000 : ℝ)|=(5305464537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2037551547/10000000000 : ℝ)|^8415 ≤ (488582008029/4000000000000 : ℝ)^6367
        have hw : |(-2037551547/10000000000 : ℝ)|=(2037551547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084153343/2000000000 : ℝ)|^8415 ≤ (44516301298477/100000000000000 : ℝ)^6367
        have hw : |(1084153343/2000000000 : ℝ)|=(1084153343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s3_6 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530546429/1000000000 : ℝ)*x 0 + (1084153341/2000000000 : ℝ)*x 1 + (-2037551897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530546429/1000000000 : ℝ)^8415 ≤ (1730765832767/4000000000000 : ℝ)^6367 := by
    have hnat : (530546429 : ℕ)^8415*4000000000000^6367 ≤ 1730765832767^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530546429 1000000000 1730765832767 4000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084153341/2000000000 : ℝ)^8415 ≤ (2225815059497/5000000000000 : ℝ)^6367 := by
    have hnat : (1084153341 : ℕ)^8415*5000000000000^6367 ≤ 2225815059497^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084153341 2000000000 2225815059497 5000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2037551897/10000000000 : ℝ)^8415 ≤ (2442910594753/20000000000000 : ℝ)^6367 := by
    have hnat : (2037551897 : ℕ)^8415*20000000000000^6367 ≤ 2442910594753^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037551897 10000000000 2442910594753 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530546429/1000000000 : ℝ), (1084153341/2000000000 : ℝ), (-2037551897/10000000000 : ℝ)] ![(1730765832767/4000000000000 : ℝ), (2225815059497/5000000000000 : ℝ), (2442910594753/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530546429/1000000000 : ℝ)|^8415 ≤ (1730765832767/4000000000000 : ℝ)^6367
        have hw : |(530546429/1000000000 : ℝ)|=(530546429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084153341/2000000000 : ℝ)|^8415 ≤ (2225815059497/5000000000000 : ℝ)^6367
        have hw : |(1084153341/2000000000 : ℝ)|=(1084153341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2037551897/10000000000 : ℝ)|^8415 ≤ (2442910594753/20000000000000 : ℝ)^6367
        have hw : |(-2037551897/10000000000 : ℝ)|=(2037551897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s3_7 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108793877/250000000 : ℝ)*x 0 + (1134615843/2500000000 : ℝ)*x 1 + (4172608311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108793877/250000000 : ℝ)^8415 ≤ (16649752340781/50000000000000 : ℝ)^6367 := by
    have hnat : (108793877 : ℕ)^8415*50000000000000^6367 ≤ 16649752340781^6367*250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108793877 250000000 16649752340781 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134615843/2500000000 : ℝ)^8415 ≤ (17600322745519/50000000000000 : ℝ)^6367 := by
    have hnat : (1134615843 : ℕ)^8415*50000000000000^6367 ≤ 17600322745519^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134615843 2500000000 17600322745519 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172608311/10000000000 : ℝ)^8415 ≤ (15749924904511/50000000000000 : ℝ)^6367 := by
    have hnat : (4172608311 : ℕ)^8415*50000000000000^6367 ≤ 15749924904511^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172608311 10000000000 15749924904511 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108793877/250000000 : ℝ), (1134615843/2500000000 : ℝ), (4172608311/10000000000 : ℝ)] ![(16649752340781/50000000000000 : ℝ), (17600322745519/50000000000000 : ℝ), (15749924904511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108793877/250000000 : ℝ)|^8415 ≤ (16649752340781/50000000000000 : ℝ)^6367
        have hw : |(108793877/250000000 : ℝ)|=(108793877/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134615843/2500000000 : ℝ)|^8415 ≤ (17600322745519/50000000000000 : ℝ)^6367
        have hw : |(1134615843/2500000000 : ℝ)|=(1134615843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172608311/10000000000 : ℝ)|^8415 ≤ (15749924904511/50000000000000 : ℝ)^6367
        have hw : |(4172608311/10000000000 : ℝ)|=(4172608311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1222_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4069/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10859/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (92/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4069/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4069/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4069/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4069/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4069/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4069/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9417/100000 : ℝ) ^ (4207/1024 : ℝ) ≤ (380455638518581/6250000000000000000 : ℝ) := by
    have hpowers : (9417/100000 : ℝ)^4207 ≤ (380455638518581/6250000000000000000 : ℝ)^1024 := by
      have hnat : (9417 : ℕ)^4207*6250000000000000000^1024 ≤ 380455638518581^1024*100000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9417 100000 380455638518581 6250000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9417/100000 : ℝ)) (X := (380455638518581/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4069/25000 : ℝ) ^ (4207/1024 : ℝ) ≤ (1440999181044723/2500000000000000000 : ℝ) := by
    have hpowers : (4069/25000 : ℝ)^4207 ≤ (1440999181044723/2500000000000000000 : ℝ)^1024 := by
      have hnat : (4069 : ℕ)^4207*2500000000000000000^1024 ≤ 1440999181044723^1024*25000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4069 25000 1440999181044723 2500000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4069/25000 : ℝ)) (X := (1440999181044723/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125380455638518581/3125000000000000000 : ℝ) ≤ (10000296320328781/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (3125380455638518581/3125000000000000000 : ℝ)^1024 ≤ (10000296320328781/10000000000000000 : ℝ)^4207 := by
      have hnat : (3125380455638518581 : ℕ)^1024*10000000000000000^4207 ≤ 10000296320328781^4207*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125380455638518581 3125000000000000000 10000296320328781 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000296320328781/10000000000000000 : ℝ)) (X := (3125380455638518581/3125000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12507965907182260777/12500000000000000000 : ℝ) ≤ (2000310154435383/2000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (12507965907182260777/12500000000000000000 : ℝ)^1024 ≤ (2000310154435383/2000000000000000 : ℝ)^4207 := by
      have hnat : (12507965907182260777 : ℕ)^1024*2000000000000000^4207 ≤ 2000310154435383^4207*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507965907182260777 12500000000000000000 2000310154435383 2000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000310154435383/2000000000000000 : ℝ)) (X := (12507965907182260777/12500000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1251440999181044723/1250000000000000000 : ℝ) ≤ (10002805224025049/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (1251440999181044723/1250000000000000000 : ℝ)^1024 ≤ (10002805224025049/10000000000000000 : ℝ)^4207 := by
      have hnat : (1251440999181044723 : ℕ)^1024*10000000000000000^4207 ≤ 10002805224025049^4207*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1251440999181044723 1250000000000000000 10002805224025049 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002805224025049/10000000000000000 : ℝ)) (X := (1251440999181044723/1250000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(380455638518581/6250000000000000000 : ℝ) ≤ ((68568406115027353123/68590000000000000000 : ℝ)+2*(627225924067/342950000000000 : ℝ)*(9417/100000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (68568406115027353123/68590000000000000000 : ℝ)+2*(627225924067/342950000000000 : ℝ)*(9417/100000 : ℝ)=(10000296320328781/10000000000000000 : ℝ) by norm_num, show 1+2*(380455638518581/6250000000000000000 : ℝ)=(3125380455638518581/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1440999181044723/2500000000000000000 : ℝ)+(380455638518581/6250000000000000000 : ℝ) ≤ ((68568406115027353123/68590000000000000000 : ℝ)+(627225924067/342950000000000 : ℝ)*((4069/25000 : ℝ)+(9417/100000 : ℝ)))^(4207/1024 : ℝ) := by
    rw [show (68568406115027353123/68590000000000000000 : ℝ)+(627225924067/342950000000000 : ℝ)*((4069/25000 : ℝ)+(9417/100000 : ℝ))=(2000310154435383/2000000000000000 : ℝ) by norm_num, show 1+(1440999181044723/2500000000000000000 : ℝ)+(380455638518581/6250000000000000000 : ℝ)=(12507965907182260777/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1440999181044723/2500000000000000000 : ℝ) ≤ ((68568406115027353123/68590000000000000000 : ℝ)+2*(627225924067/342950000000000 : ℝ)*(4069/25000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (68568406115027353123/68590000000000000000 : ℝ)+2*(627225924067/342950000000000 : ℝ)*(4069/25000 : ℝ)=(10002805224025049/10000000000000000 : ℝ) by norm_num, show 1+2*(1440999181044723/2500000000000000000 : ℝ)=(1251440999181044723/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68568406115027353123/68590000000000000000 : ℝ)*(X 1 0+X 2 0)+(627225924067/342950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (9417/100000 : ℝ)) (hi := (4069/25000 : ℝ)) (c := (68568406115027353123/68590000000000000000 : ℝ)) (alpha := (627225924067/342950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68568406115027353123/68590000000000000000 : ℝ)*(X 0 1+X 2 1)+(627225924067/342950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (9417/100000 : ℝ)) (hi := (4069/25000 : ℝ)) (c := (68568406115027353123/68590000000000000000 : ℝ)) (alpha := (627225924067/342950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68568406115027353123/68590000000000000000 : ℝ)*(X 0 2+X 1 2)+(627225924067/342950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (9417/100000 : ℝ)) (hi := (4069/25000 : ℝ)) (c := (68568406115027353123/68590000000000000000 : ℝ)) (alpha := (627225924067/342950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-212619089/1000000000 : ℝ)*X 0 0+(5421441897/10000000000 : ℝ)*X 0 1+(523904519/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070387027/2000000000 : ℝ)*X 1 0+(-2219273247/10000000000 : ℝ)*X 1 1+(2619522699/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351934999/10000000000 : ℝ)*X 2 0+(5239045791/10000000000 : ℝ)*X 2 1+(-2219272909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175862531/5000000000 : ℝ)*X 0 0+(4171244831/10000000000 : ℝ)*X 0 1+(907963993/2000000000 : ℝ)*X 0 2+(2175862531/5000000000 : ℝ)*X 1 0+(4171244831/10000000000 : ℝ)*X 1 1+(907963993/2000000000 : ℝ)*X 1 2+(2175862531/5000000000 : ℝ)*X 2 0+(4171244831/10000000000 : ℝ)*X 2 1+(907963993/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-531551443/2500000000 : ℝ)*X 0 0+(5239716339/10000000000 : ℝ)*X 0 1+(1084153411/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305464537/10000000000 : ℝ)*X 1 0+(-2037551547/10000000000 : ℝ)*X 1 1+(1084153343/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530546429/1000000000 : ℝ)*X 2 0+(1084153341/2000000000 : ℝ)*X 2 1+(-2037551897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108793877/250000000 : ℝ)*X 0 0+(1134615843/2500000000 : ℝ)*X 0 1+(4172608311/10000000000 : ℝ)*X 0 2+(108793877/250000000 : ℝ)*X 1 0+(1134615843/2500000000 : ℝ)*X 1 1+(4172608311/10000000000 : ℝ)*X 1 2+(108793877/250000000 : ℝ)*X 2 0+(1134615843/2500000000 : ℝ)*X 2 1+(4172608311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1731591241090639354922509461/214343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (282410259/25000000000000 : ℝ)*(base19) + (91454881/12500000000000 : ℝ)*(base23) + (139009167/100000000000000 : ℝ)*(lower2) + (1228357/781250000000 : ℝ)*(upper5) + (512237166420819/12500000000000 : ℝ)*(major0) + (512237166420819/12500000000000 : ℝ)*(major1) + (512237166420819/12500000000000 : ℝ)*(major2) + (2741291765484061/50000000000000 : ℝ)*(sp0) + (5482618272379087/100000000000000 : ℝ)*(sp1) + (2741309395949483/50000000000000 : ℝ)*(sp2) + (271316375011483/10000000000000 : ℝ)*(sp3) + (8998142473/25000000000000 : ℝ)*(sp4) + (121517891/100000000000000 : ℝ)*(sp5) + (5559897273/50000000000000 : ℝ)*(sp7) + (21196678671167/781250000000 : ℝ)*(f.failure) + (2741309761769007/50000000000000 : ℝ)*(f.sum) + (3983748590643/535859375000000000000000000 : ℝ)*base66 + (13005983815865532263/857375000000000000000000000000000 : ℝ)*base68 + (4369395372014032263/857375000000000000000000000000000 : ℝ)*base70 + (3513497076989532263/857375000000000000000000000000000 : ℝ)*base72 + (31971424932869/4286875000000000000000000000 : ℝ)*base74 + (16477801087690157263/857375000000000000000000000000000 : ℝ)*base76 + (9293283002126782263/857375000000000000000000000000000 : ℝ)*base78 + (1204595883014967737/857375000000000000000000000000000 : ℝ)*base79 + (20817407394661/17147500000000000000000000000 : ℝ)*base82 + (331663/39062500000000000000 : ℝ)*base89 + (331663/39062500000000000000 : ℝ)*base91 + (331663/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (887006977925613083195061123/85737500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (595570197/25000000000000 : ℝ)*(base19) + (141084209/6250000000000 : ℝ)*(base23) + (66111551/100000000000000 : ℝ)*(upper3) + (17595951/12500000000000 : ℝ)*(lower4) + (373783113/100000000000000 : ℝ)*(upper5) + (103207947701333/2500000000000 : ℝ)*(major0) + (103207947701333/2500000000000 : ℝ)*(major1) + (103207947701333/2500000000000 : ℝ)*(major2) + (46059402993/100000000000000 : ℝ)*(sp1) + (30861618903/100000000000000 : ℝ)*(sp2) + (5523319456380463/100000000000000 : ℝ)*(sp4) + (2761635507348341/50000000000000 : ℝ)*(sp5) + (5523286337414217/100000000000000 : ℝ)*(sp6) + (2733316014872411/100000000000000 : ℝ)*(sp7) + (2733316014872411/100000000000000 : ℝ)*(f.failure) + (5523319456380463/100000000000000 : ℝ)*(f.sum) + (1592309621029/342950000000000000000000000 : ℝ)*base65 + (269018945341262041/171475000000000000000000000000000 : ℝ)*base68 + (947880924699162959/171475000000000000000000000000000 : ℝ)*base69 + (812335272986737959/171475000000000000000000000000000 : ℝ)*base71 + (21742276894077/6859000000000000000000000000 : ℝ)*base74 + (4148535640435137959/171475000000000000000000000000000 : ℝ)*base75 + (45143821713187959/171475000000000000000000000000000 : ℝ)*base77 + (394872558780237041/171475000000000000000000000000000 : ℝ)*base80 + (2774088116379/6859000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6506979/5000000000000000000000 : ℝ)*base89 + (6506979/5000000000000000000000 : ℝ)*base91 + (6506979/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1222_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4069/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10859/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1222_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1222_s4_0 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-532152239/2500000000 : ℝ)*x 0 + (1349579913/2500000000 : ℝ)*x 1 + (5260583543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532152239/2500000000 : ℝ)^8415 ≤ (6470564709991/50000000000000 : ℝ)^6367 := by
    have hnat : (532152239 : ℕ)^8415*50000000000000^6367 ≤ 6470564709991^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532152239 2500000000 6470564709991 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349579913/2500000000 : ℝ)^8415 ≤ (44272830124209/100000000000000 : ℝ)^6367 := by
    have hnat : (1349579913 : ℕ)^8415*100000000000000^6367 ≤ 44272830124209^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349579913 2500000000 44272830124209 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260583543/10000000000 : ℝ)^8415 ≤ (42786040440021/100000000000000 : ℝ)^6367 := by
    have hnat : (5260583543 : ℕ)^8415*100000000000000^6367 ≤ 42786040440021^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260583543 10000000000 42786040440021 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532152239/2500000000 : ℝ), (1349579913/2500000000 : ℝ), (5260583543/10000000000 : ℝ)] ![(6470564709991/50000000000000 : ℝ), (44272830124209/100000000000000 : ℝ), (42786040440021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532152239/2500000000 : ℝ)|^8415 ≤ (6470564709991/50000000000000 : ℝ)^6367
        have hw : |(-532152239/2500000000 : ℝ)|=(532152239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349579913/2500000000 : ℝ)|^8415 ≤ (44272830124209/100000000000000 : ℝ)^6367
        have hw : |(1349579913/2500000000 : ℝ)|=(1349579913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260583543/10000000000 : ℝ)|^8415 ≤ (42786040440021/100000000000000 : ℝ)^6367
        have hw : |(5260583543/10000000000 : ℝ)|=(5260583543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s4_1 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346117437/10000000000 : ℝ)*x 0 + (-2198551637/10000000000 : ℝ)*x 1 + (263029173/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346117437/10000000000 : ℝ)^8415 ≤ (43707880857291/100000000000000 : ℝ)^6367 := by
    have hnat : (5346117437 : ℕ)^8415*100000000000000^6367 ≤ 43707880857291^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346117437 10000000000 43707880857291 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198551637/10000000000 : ℝ)^8415 ≤ (270121591573/2000000000000 : ℝ)^6367 := by
    have hnat : (2198551637 : ℕ)^8415*2000000000000^6367 ≤ 270121591573^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198551637 10000000000 270121591573 2000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263029173/500000000 : ℝ)^8415 ≤ (21393019773907/50000000000000 : ℝ)^6367 := by
    have hnat : (263029173 : ℕ)^8415*50000000000000^6367 ≤ 21393019773907^6367*500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263029173 500000000 21393019773907 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346117437/10000000000 : ℝ), (-2198551637/10000000000 : ℝ), (263029173/500000000 : ℝ)] ![(43707880857291/100000000000000 : ℝ), (270121591573/2000000000000 : ℝ), (21393019773907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346117437/10000000000 : ℝ)|^8415 ≤ (43707880857291/100000000000000 : ℝ)^6367
        have hw : |(5346117437/10000000000 : ℝ)|=(5346117437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2198551637/10000000000 : ℝ)|^8415 ≤ (270121591573/2000000000000 : ℝ)^6367
        have hw : |(-2198551637/10000000000 : ℝ)|=(2198551637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263029173/500000000 : ℝ)|^8415 ≤ (21393019773907/50000000000000 : ℝ)^6367
        have hw : |(263029173/500000000 : ℝ)|=(263029173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s4_2 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534611719/1000000000 : ℝ)*x 0 + (1052116697/2000000000 : ℝ)*x 1 + (-2198551933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534611719/1000000000 : ℝ)^8415 ≤ (43707878188359/100000000000000 : ℝ)^6367 := by
    have hnat : (534611719 : ℕ)^8415*100000000000000^6367 ≤ 43707878188359^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534611719 1000000000 43707878188359 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052116697/2000000000 : ℝ)^8415 ≤ (42786039816551/100000000000000 : ℝ)^6367 := by
    have hnat : (1052116697 : ℕ)^8415*100000000000000^6367 ≤ 42786039816551^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052116697 2000000000 42786039816551 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198551933/10000000000 : ℝ)^8415 ≤ (6753040990963/50000000000000 : ℝ)^6367 := by
    have hnat : (2198551933 : ℕ)^8415*50000000000000^6367 ≤ 6753040990963^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198551933 10000000000 6753040990963 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534611719/1000000000 : ℝ), (1052116697/2000000000 : ℝ), (-2198551933/10000000000 : ℝ)] ![(43707878188359/100000000000000 : ℝ), (42786039816551/100000000000000 : ℝ), (6753040990963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534611719/1000000000 : ℝ)|^8415 ≤ (43707878188359/100000000000000 : ℝ)^6367
        have hw : |(534611719/1000000000 : ℝ)|=(534611719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052116697/2000000000 : ℝ)|^8415 ≤ (42786039816551/100000000000000 : ℝ)^6367
        have hw : |(1052116697/2000000000 : ℝ)|=(1052116697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2198551933/10000000000 : ℝ)|^8415 ≤ (6753040990963/50000000000000 : ℝ)^6367
        have hw : |(-2198551933/10000000000 : ℝ)|=(2198551933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s4_3 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353174321/10000000000 : ℝ)*x 0 + (4216182631/10000000000 : ℝ)*x 1 + (4494511343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353174321/10000000000 : ℝ)^8415 ≤ (33313858634731/100000000000000 : ℝ)^6367 := by
    have hnat : (4353174321 : ℕ)^8415*100000000000000^6367 ≤ 33313858634731^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353174321 10000000000 33313858634731 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4216182631/10000000000 : ℝ)^8415 ≤ (31935339461737/100000000000000 : ℝ)^6367 := by
    have hnat : (4216182631 : ℕ)^8415*100000000000000^6367 ≤ 31935339461737^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216182631 10000000000 31935339461737 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494511343/10000000000 : ℝ)^8415 ≤ (34750801886963/100000000000000 : ℝ)^6367 := by
    have hnat : (4494511343 : ℕ)^8415*100000000000000^6367 ≤ 34750801886963^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494511343 10000000000 34750801886963 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353174321/10000000000 : ℝ), (4216182631/10000000000 : ℝ), (4494511343/10000000000 : ℝ)] ![(33313858634731/100000000000000 : ℝ), (31935339461737/100000000000000 : ℝ), (34750801886963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353174321/10000000000 : ℝ)|^8415 ≤ (33313858634731/100000000000000 : ℝ)^6367
        have hw : |(4353174321/10000000000 : ℝ)|=(4353174321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4216182631/10000000000 : ℝ)|^8415 ≤ (31935339461737/100000000000000 : ℝ)^6367
        have hw : |(4216182631/10000000000 : ℝ)|=(4216182631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494511343/10000000000 : ℝ)|^8415 ≤ (34750801886963/100000000000000 : ℝ)^6367
        have hw : |(4494511343/10000000000 : ℝ)|=(4494511343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s4_4 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064307607/5000000000 : ℝ)*x 0 + (526096701/1000000000 : ℝ)*x 1 + (5397934711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064307607/5000000000 : ℝ)^8415 ≤ (12941179704157/100000000000000 : ℝ)^6367 := by
    have hnat : (1064307607 : ℕ)^8415*100000000000000^6367 ≤ 12941179704157^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064307607 5000000000 12941179704157 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526096701/1000000000 : ℝ)^8415 ≤ (5348770319887/12500000000000 : ℝ)^6367 := by
    have hnat : (526096701 : ℕ)^8415*12500000000000^6367 ≤ 5348770319887^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526096701 1000000000 5348770319887 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397934711/10000000000 : ℝ)^8415 ≤ (44268657712573/100000000000000 : ℝ)^6367 := by
    have hnat : (5397934711 : ℕ)^8415*100000000000000^6367 ≤ 44268657712573^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397934711 10000000000 44268657712573 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064307607/5000000000 : ℝ), (526096701/1000000000 : ℝ), (5397934711/10000000000 : ℝ)] ![(12941179704157/100000000000000 : ℝ), (5348770319887/12500000000000 : ℝ), (44268657712573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064307607/5000000000 : ℝ)|^8415 ≤ (12941179704157/100000000000000 : ℝ)^6367
        have hw : |(-1064307607/5000000000 : ℝ)|=(1064307607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526096701/1000000000 : ℝ)|^8415 ≤ (5348770319887/12500000000000 : ℝ)^6367
        have hw : |(526096701/1000000000 : ℝ)|=(526096701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397934711/10000000000 : ℝ)|^8415 ≤ (44268657712573/100000000000000 : ℝ)^6367
        have hw : |(5397934711/10000000000 : ℝ)|=(5397934711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s4_5 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655511463/5000000000 : ℝ)*x 0 + (-2061200599/10000000000 : ℝ)*x 1 + (1349483691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655511463/5000000000 : ℝ)^8415 ≤ (21664535930229/50000000000000 : ℝ)^6367 := by
    have hnat : (2655511463 : ℕ)^8415*50000000000000^6367 ≤ 21664535930229^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655511463 5000000000 21664535930229 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061200599/10000000000 : ℝ)^8415 ≤ (12402269835821/100000000000000 : ℝ)^6367 := by
    have hnat : (2061200599 : ℕ)^8415*100000000000000^6367 ≤ 12402269835821^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061200599 10000000000 12402269835821 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349483691/2500000000 : ℝ)^8415 ≤ (22134329143519/50000000000000 : ℝ)^6367 := by
    have hnat : (1349483691 : ℕ)^8415*50000000000000^6367 ≤ 22134329143519^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349483691 2500000000 22134329143519 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655511463/5000000000 : ℝ), (-2061200599/10000000000 : ℝ), (1349483691/2500000000 : ℝ)] ![(21664535930229/50000000000000 : ℝ), (12402269835821/100000000000000 : ℝ), (22134329143519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655511463/5000000000 : ℝ)|^8415 ≤ (21664535930229/50000000000000 : ℝ)^6367
        have hw : |(2655511463/5000000000 : ℝ)|=(2655511463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2061200599/10000000000 : ℝ)|^8415 ≤ (12402269835821/100000000000000 : ℝ)^6367
        have hw : |(-2061200599/10000000000 : ℝ)|=(2061200599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349483691/2500000000 : ℝ)|^8415 ≤ (22134329143519/50000000000000 : ℝ)^6367
        have hw : |(1349483691/2500000000 : ℝ)|=(1349483691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s4_6 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (82984731/156250000 : ℝ)*x 0 + (84342733/156250000 : ℝ)*x 1 + (-2061200591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82984731/156250000 : ℝ)^8415 ≤ (43329070329339/100000000000000 : ℝ)^6367 := by
    have hnat : (82984731 : ℕ)^8415*100000000000000^6367 ≤ 43329070329339^6367*156250000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82984731 156250000 43329070329339 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84342733/156250000 : ℝ)^8415 ≤ (8853731978241/20000000000000 : ℝ)^6367 := by
    have hnat : (84342733 : ℕ)^8415*20000000000000^6367 ≤ 8853731978241^6367*156250000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84342733 156250000 8853731978241 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061200591/10000000000 : ℝ)^8415 ≤ (6201134886101/50000000000000 : ℝ)^6367 := by
    have hnat : (2061200591 : ℕ)^8415*50000000000000^6367 ≤ 6201134886101^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061200591 10000000000 6201134886101 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82984731/156250000 : ℝ), (84342733/156250000 : ℝ), (-2061200591/10000000000 : ℝ)] ![(43329070329339/100000000000000 : ℝ), (8853731978241/20000000000000 : ℝ), (6201134886101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82984731/156250000 : ℝ)|^8415 ≤ (43329070329339/100000000000000 : ℝ)^6367
        have hw : |(82984731/156250000 : ℝ)|=(82984731/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84342733/156250000 : ℝ)|^8415 ≤ (8853731978241/20000000000000 : ℝ)^6367
        have hw : |(84342733/156250000 : ℝ)|=(84342733/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2061200591/10000000000 : ℝ)|^8415 ≤ (6201134886101/50000000000000 : ℝ)^6367
        have hw : |(-2061200591/10000000000 : ℝ)|=(2061200591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s4_7 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34009277/78125000 : ℝ)*x 0 + (4493736617/10000000000 : ℝ)*x 1 + (4216960137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34009277/78125000 : ℝ)^8415 ≤ (8328497871709/25000000000000 : ℝ)^6367 := by
    have hnat : (34009277 : ℕ)^8415*25000000000000^6367 ≤ 8328497871709^6367*78125000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34009277 78125000 8328497871709 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493736617/10000000000 : ℝ)^8415 ≤ (17371442652513/50000000000000 : ℝ)^6367 := by
    have hnat : (4493736617 : ℕ)^8415*50000000000000^6367 ≤ 17371442652513^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493736617 10000000000 17371442652513 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4216960137/10000000000 : ℝ)^8415 ≤ (15971561598187/50000000000000 : ℝ)^6367 := by
    have hnat : (4216960137 : ℕ)^8415*50000000000000^6367 ≤ 15971561598187^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216960137 10000000000 15971561598187 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34009277/78125000 : ℝ), (4493736617/10000000000 : ℝ), (4216960137/10000000000 : ℝ)] ![(8328497871709/25000000000000 : ℝ), (17371442652513/50000000000000 : ℝ), (15971561598187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34009277/78125000 : ℝ)|^8415 ≤ (8328497871709/25000000000000 : ℝ)^6367
        have hw : |(34009277/78125000 : ℝ)|=(34009277/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493736617/10000000000 : ℝ)|^8415 ≤ (17371442652513/50000000000000 : ℝ)^6367
        have hw : |(4493736617/10000000000 : ℝ)|=(4493736617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4216960137/10000000000 : ℝ)|^8415 ≤ (15971561598187/50000000000000 : ℝ)^6367
        have hw : |(4216960137/10000000000 : ℝ)|=(4216960137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1222_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10859/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5659/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10859/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10859/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10859/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10859/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10859/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10859/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10859/100000 : ℝ) ^ (4207/1024 : ℝ) ≤ (5465255391326839/50000000000000000000 : ℝ) := by
    have hpowers : (10859/100000 : ℝ)^4207 ≤ (5465255391326839/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10859 : ℕ)^4207*50000000000000000000^1024 ≤ 5465255391326839^1024*100000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10859 100000 5465255391326839 50000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10859/100000 : ℝ)) (X := (5465255391326839/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (92/625 : ℝ) ^ (4207/1024 : ℝ) ≤ (38144659873673807/100000000000000000000 : ℝ) := by
    have hpowers : (92/625 : ℝ)^4207 ≤ (38144659873673807/100000000000000000000 : ℝ)^1024 := by
      have hnat : (92 : ℕ)^4207*100000000000000000000^1024 ≤ 38144659873673807^1024*625^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92 625 38144659873673807 100000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92/625 : ℝ)) (X := (38144659873673807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005465255391326839/25000000000000000000 : ℝ) ≤ (2500133015420891/2500000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (25005465255391326839/25000000000000000000 : ℝ)^1024 ≤ (2500133015420891/2500000000000000 : ℝ)^4207 := by
      have hnat : (25005465255391326839 : ℕ)^1024*2500000000000000^4207 ≤ 2500133015420891^4207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005465255391326839 25000000000000000000 2500133015420891 2500000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500133015420891/2500000000000000 : ℝ)) (X := (25005465255391326839/25000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009815034131265497/20000000000000000000 : ℝ) ≤ (2000238857370791/2000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (20009815034131265497/20000000000000000000 : ℝ)^1024 ≤ (2000238857370791/2000000000000000 : ℝ)^4207 := by
      have hnat : (20009815034131265497 : ℕ)^1024*2000000000000000^4207 ≤ 2000238857370791^4207*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009815034131265497 20000000000000000000 2000238857370791 2000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000238857370791/2000000000000000 : ℝ)) (X := (20009815034131265497/20000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038144659873673807/50000000000000000000 : ℝ) ≤ (5000928256012173/5000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (50038144659873673807/50000000000000000000 : ℝ)^1024 ≤ (5000928256012173/5000000000000000 : ℝ)^4207 := by
      have hnat : (50038144659873673807 : ℕ)^1024*5000000000000000^4207 ≤ 5000928256012173^4207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038144659873673807 50000000000000000000 5000928256012173 5000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000928256012173/5000000000000000 : ℝ)) (X := (50038144659873673807/50000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5465255391326839/50000000000000000000 : ℝ) ≤ ((19298836041954844433/19305000000000000000 : ℝ)+2*(662225170391/386100000000000 : ℝ)*(10859/100000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (19298836041954844433/19305000000000000000 : ℝ)+2*(662225170391/386100000000000 : ℝ)*(10859/100000 : ℝ)=(2500133015420891/2500000000000000 : ℝ) by norm_num, show 1+2*(5465255391326839/50000000000000000000 : ℝ)=(25005465255391326839/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38144659873673807/100000000000000000000 : ℝ)+(5465255391326839/50000000000000000000 : ℝ) ≤ ((19298836041954844433/19305000000000000000 : ℝ)+(662225170391/386100000000000 : ℝ)*((92/625 : ℝ)+(10859/100000 : ℝ)))^(4207/1024 : ℝ) := by
    rw [show (19298836041954844433/19305000000000000000 : ℝ)+(662225170391/386100000000000 : ℝ)*((92/625 : ℝ)+(10859/100000 : ℝ))=(2000238857370791/2000000000000000 : ℝ) by norm_num, show 1+(38144659873673807/100000000000000000000 : ℝ)+(5465255391326839/50000000000000000000 : ℝ)=(20009815034131265497/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38144659873673807/100000000000000000000 : ℝ) ≤ ((19298836041954844433/19305000000000000000 : ℝ)+2*(662225170391/386100000000000 : ℝ)*(92/625 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (19298836041954844433/19305000000000000000 : ℝ)+2*(662225170391/386100000000000 : ℝ)*(92/625 : ℝ)=(5000928256012173/5000000000000000 : ℝ) by norm_num, show 1+2*(38144659873673807/100000000000000000000 : ℝ)=(50038144659873673807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19298836041954844433/19305000000000000000 : ℝ)*(X 1 0+X 2 0)+(662225170391/386100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (10859/100000 : ℝ)) (hi := (92/625 : ℝ)) (c := (19298836041954844433/19305000000000000000 : ℝ)) (alpha := (662225170391/386100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19298836041954844433/19305000000000000000 : ℝ)*(X 0 1+X 2 1)+(662225170391/386100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (10859/100000 : ℝ)) (hi := (92/625 : ℝ)) (c := (19298836041954844433/19305000000000000000 : ℝ)) (alpha := (662225170391/386100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19298836041954844433/19305000000000000000 : ℝ)*(X 0 2+X 1 2)+(662225170391/386100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (10859/100000 : ℝ)) (hi := (92/625 : ℝ)) (c := (19298836041954844433/19305000000000000000 : ℝ)) (alpha := (662225170391/386100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-532152239/2500000000 : ℝ)*X 0 0+(1349579913/2500000000 : ℝ)*X 0 1+(5260583543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346117437/10000000000 : ℝ)*X 1 0+(-2198551637/10000000000 : ℝ)*X 1 1+(263029173/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534611719/1000000000 : ℝ)*X 2 0+(1052116697/2000000000 : ℝ)*X 2 1+(-2198551933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353174321/10000000000 : ℝ)*X 0 0+(4216182631/10000000000 : ℝ)*X 0 1+(4494511343/10000000000 : ℝ)*X 0 2+(4353174321/10000000000 : ℝ)*X 1 0+(4216182631/10000000000 : ℝ)*X 1 1+(4494511343/10000000000 : ℝ)*X 1 2+(4353174321/10000000000 : ℝ)*X 2 0+(4216182631/10000000000 : ℝ)*X 2 1+(4494511343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1064307607/5000000000 : ℝ)*X 0 0+(526096701/1000000000 : ℝ)*X 0 1+(5397934711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655511463/5000000000 : ℝ)*X 1 0+(-2061200599/10000000000 : ℝ)*X 1 1+(1349483691/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82984731/156250000 : ℝ)*X 2 0+(84342733/156250000 : ℝ)*X 2 1+(-2061200591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34009277/78125000 : ℝ)*X 0 0+(4493736617/10000000000 : ℝ)*X 0 1+(4216960137/10000000000 : ℝ)*X 0 2+(34009277/78125000 : ℝ)*X 1 0+(4493736617/10000000000 : ℝ)*X 1 1+(4216960137/10000000000 : ℝ)*X 1 2+(34009277/78125000 : ℝ)*X 2 0+(4493736617/10000000000 : ℝ)*X 2 1+(4216960137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62074000843712275229549167/6187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2433379053/100000000000000 : ℝ)*(base19) + (2224055197/100000000000000 : ℝ)*(base23) + (118300511/100000000000000 : ℝ)*(upper2) + (412651763/100000000000000 : ℝ)*(upper3) + (10175219/20000000000000 : ℝ)*(upper4) + (1356664659554587/25000000000000 : ℝ)*(major0) + (1356664659554587/25000000000000 : ℝ)*(major1) + (1356664659554587/25000000000000 : ℝ)*(major2) + (3630166801890443/50000000000000 : ℝ)*(sp0) + (1815095176309331/25000000000000 : ℝ)*(sp1) + (7260380914561181/100000000000000 : ℝ)*(sp2) + (1796450548913821/50000000000000 : ℝ)*(sp3) + (12383708873/25000000000000 : ℝ)*(sp4) + (32705587273/100000000000000 : ℝ)*(sp7) + (1796466901707457/50000000000000 : ℝ)*(f.failure) + (3630191569308189/50000000000000 : ℝ)*(f.sum) + (48624717095531/9652500000000000000000000000 : ℝ)*base66 + (364990744408671019/53625000000000000000000000000000 : ℝ)*base67 + (18768491201078981/53625000000000000000000000000000 : ℝ)*base70 + (577554163699703981/53625000000000000000000000000000 : ℝ)*base72 + (4448844631793/19305000000000000000000000000 : ℝ)*base73 + (807167022952671019/53625000000000000000000000000000 : ℝ)*base75 + (362581341456953981/53625000000000000000000000000000 : ℝ)*base78 + (21420559065953981/53625000000000000000000000000000 : ℝ)*base80 + (23465750632901/9652500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (27327527/2500000000000000000000 : ℝ)*base90 + (27327527/2500000000000000000000 : ℝ)*base92 + (27327527/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43138932984803552578361627/4468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (952856233/50000000000000 : ℝ)*(base19) + (873742023/50000000000000 : ℝ)*(base23) + (73688623/25000000000000 : ℝ)*(upper3) + (441749/12500000000000 : ℝ)*(lower4) + (19550657/12500000000000 : ℝ)*(upper5) + (1364251139753379/25000000000000 : ℝ)*(major0) + (1364251139753379/25000000000000 : ℝ)*(major1) + (1364251139753379/25000000000000 : ℝ)*(major2) + (9041953171/20000000000000 : ℝ)*(sp1) + (12449700103/25000000000000 : ℝ)*(sp2) + (7300983276750129/100000000000000 : ℝ)*(sp4) + (891227558749/12207031250 : ℝ)*(sp5) + (730093173046567/10000000000000 : ℝ)*(sp6) + (3613025519494647/100000000000000 : ℝ)*(sp7) + (3613025519494647/100000000000000 : ℝ)*(f.failure) + (7300983276750129/100000000000000 : ℝ)*(f.sum) + (3159212475971/3217500000000000000000000000 : ℝ)*base65 + (146942749828219041/17875000000000000000000000000000 : ℝ)*base67 + (21973870705155959/17875000000000000000000000000000 : ℝ)*base70 + (13414741178469041/17875000000000000000000000000000 : ℝ)*base71 + (918816678277/402187500000000000000000000 : ℝ)*base73 + (165011787207469041/17875000000000000000000000000000 : ℝ)*base75 + (39084604737094041/17875000000000000000000000000000 : ℝ)*base77 + (46724371389469041/17875000000000000000000000000000 : ℝ)*base79 + (3247682546497/6435000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (14971617/5000000000000000000000 : ℝ)*base90 + (14971617/5000000000000000000000 : ℝ)*base92 + (14971617/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1222_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10859/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1222_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1222_s5_0 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129092221/10000000000 : ℝ)*x 0 + (1348224669/2500000000 : ℝ)*x 1 + (1316421711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129092221/10000000000 : ℝ)^8415 ≤ (12945012682629/100000000000000 : ℝ)^6367 := by
    have hnat : (2129092221 : ℕ)^8415*100000000000000^6367 ≤ 12945012682629^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129092221 10000000000 12945012682629 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348224669/2500000000 : ℝ)^8415 ≤ (22107040237283/50000000000000 : ℝ)^6367 := by
    have hnat : (1348224669 : ℕ)^8415*50000000000000^6367 ≤ 22107040237283^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348224669 2500000000 22107040237283 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316421711/2500000000 : ℝ)^8415 ≤ (10710226706961/25000000000000 : ℝ)^6367 := by
    have hnat : (1316421711 : ℕ)^8415*25000000000000^6367 ≤ 10710226706961^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316421711 2500000000 10710226706961 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129092221/10000000000 : ℝ), (1348224669/2500000000 : ℝ), (1316421711/2500000000 : ℝ)] ![(12945012682629/100000000000000 : ℝ), (22107040237283/50000000000000 : ℝ), (10710226706961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129092221/10000000000 : ℝ)|^8415 ≤ (12945012682629/100000000000000 : ℝ)^6367
        have hw : |(-2129092221/10000000000 : ℝ)|=(2129092221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348224669/2500000000 : ℝ)|^8415 ≤ (22107040237283/50000000000000 : ℝ)^6367
        have hw : |(1348224669/2500000000 : ℝ)|=(1348224669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316421711/2500000000 : ℝ)|^8415 ≤ (10710226706961/25000000000000 : ℝ)^6367
        have hw : |(1316421711/2500000000 : ℝ)|=(1316421711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s5_1 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672373773/5000000000 : ℝ)*x 0 + (-438723027/2000000000 : ℝ)*x 1 + (5265686859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672373773/5000000000 : ℝ)^8415 ≤ (5461634907263/12500000000000 : ℝ)^6367 := by
    have hnat : (2672373773 : ℕ)^8415*12500000000000^6367 ≤ 5461634907263^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672373773 5000000000 5461634907263 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438723027/2000000000 : ℝ)^8415 ≤ (841625858491/6250000000000 : ℝ)^6367 := by
    have hnat : (438723027 : ℕ)^8415*6250000000000^6367 ≤ 841625858491^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438723027 2000000000 841625858491 6250000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265686859/10000000000 : ℝ)^8415 ≤ (2677556686821/6250000000000 : ℝ)^6367 := by
    have hnat : (5265686859 : ℕ)^8415*6250000000000^6367 ≤ 2677556686821^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265686859 10000000000 2677556686821 6250000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672373773/5000000000 : ℝ), (-438723027/2000000000 : ℝ), (5265686859/10000000000 : ℝ)] ![(5461634907263/12500000000000 : ℝ), (841625858491/6250000000000 : ℝ), (2677556686821/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672373773/5000000000 : ℝ)|^8415 ≤ (5461634907263/12500000000000 : ℝ)^6367
        have hw : |(2672373773/5000000000 : ℝ)|=(2672373773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438723027/2000000000 : ℝ)|^8415 ≤ (841625858491/6250000000000 : ℝ)^6367
        have hw : |(-438723027/2000000000 : ℝ)|=(438723027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265686859/10000000000 : ℝ)|^8415 ≤ (2677556686821/6250000000000 : ℝ)^6367
        have hw : |(5265686859/10000000000 : ℝ)|=(5265686859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s5_2 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336186891/2500000000 : ℝ)*x 0 + (5265686937/10000000000 : ℝ)*x 1 + (-2193615007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336186891/2500000000 : ℝ)^8415 ≤ (8738615890517/20000000000000 : ℝ)^6367 := by
    have hnat : (1336186891 : ℕ)^8415*20000000000000^6367 ≤ 8738615890517^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336186891 2500000000 8738615890517 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265686937/10000000000 : ℝ)^8415 ≤ (42840907827857/100000000000000 : ℝ)^6367 := by
    have hnat : (5265686937 : ℕ)^8415*100000000000000^6367 ≤ 42840907827857^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265686937 10000000000 42840907827857 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2193615007/10000000000 : ℝ)^8415 ≤ (13466012697353/100000000000000 : ℝ)^6367 := by
    have hnat : (2193615007 : ℕ)^8415*100000000000000^6367 ≤ 13466012697353^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193615007 10000000000 13466012697353 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336186891/2500000000 : ℝ), (5265686937/10000000000 : ℝ), (-2193615007/10000000000 : ℝ)] ![(8738615890517/20000000000000 : ℝ), (42840907827857/100000000000000 : ℝ), (13466012697353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336186891/2500000000 : ℝ)|^8415 ≤ (8738615890517/20000000000000 : ℝ)^6367
        have hw : |(1336186891/2500000000 : ℝ)|=(1336186891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265686937/10000000000 : ℝ)|^8415 ≤ (42840907827857/100000000000000 : ℝ)^6367
        have hw : |(5265686937/10000000000 : ℝ)|=(5265686937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2193615007/10000000000 : ℝ)|^8415 ≤ (13466012697353/100000000000000 : ℝ)^6367
        have hw : |(-2193615007/10000000000 : ℝ)|=(2193615007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s5_3 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435345733/1000000000 : ℝ)*x 0 + (1056694981/2500000000 : ℝ)*x 1 + (70060021/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435345733/1000000000 : ℝ)^8415 ≤ (266533768943/800000000000 : ℝ)^6367 := by
    have hnat : (435345733 : ℕ)^8415*800000000000^6367 ≤ 266533768943^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435345733 1000000000 266533768943 800000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056694981/2500000000 : ℝ)^8415 ≤ (32041470340287/100000000000000 : ℝ)^6367 := by
    have hnat : (1056694981 : ℕ)^8415*100000000000000^6367 ≤ 32041470340287^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056694981 2500000000 32041470340287 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70060021/156250000 : ℝ)^8415 ≤ (34641808522143/100000000000000 : ℝ)^6367 := by
    have hnat : (70060021 : ℕ)^8415*100000000000000^6367 ≤ 34641808522143^6367*156250000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70060021 156250000 34641808522143 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435345733/1000000000 : ℝ), (1056694981/2500000000 : ℝ), (70060021/156250000 : ℝ)] ![(266533768943/800000000000 : ℝ), (32041470340287/100000000000000 : ℝ), (34641808522143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435345733/1000000000 : ℝ)|^8415 ≤ (266533768943/800000000000 : ℝ)^6367
        have hw : |(435345733/1000000000 : ℝ)|=(435345733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056694981/2500000000 : ℝ)|^8415 ≤ (32041470340287/100000000000000 : ℝ)^6367
        have hw : |(1056694981/2500000000 : ℝ)|=(1056694981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70060021/156250000 : ℝ)|^8415 ≤ (34641808522143/100000000000000 : ℝ)^6367
        have hw : |(70060021/156250000 : ℝ)|=(70060021/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s5_4 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064548551/5000000000 : ℝ)*x 0 + (5266014267/10000000000 : ℝ)*x 1 + (5392570131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064548551/5000000000 : ℝ)^8415 ≤ (12945051905217/100000000000000 : ℝ)^6367 := by
    have hnat : (1064548551 : ℕ)^8415*100000000000000^6367 ≤ 12945051905217^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064548551 5000000000 12945051905217 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266014267/10000000000 : ℝ)^8415 ≤ (10711106896967/25000000000000 : ℝ)^6367 := by
    have hnat : (5266014267 : ℕ)^8415*25000000000000^6367 ≤ 10711106896967^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266014267 10000000000 10711106896967 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392570131/10000000000 : ℝ)^8415 ≤ (44210520489189/100000000000000 : ℝ)^6367 := by
    have hnat : (5392570131 : ℕ)^8415*100000000000000^6367 ≤ 44210520489189^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392570131 10000000000 44210520489189 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064548551/5000000000 : ℝ), (5266014267/10000000000 : ℝ), (5392570131/10000000000 : ℝ)] ![(12945051905217/100000000000000 : ℝ), (10711106896967/25000000000000 : ℝ), (44210520489189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064548551/5000000000 : ℝ)|^8415 ≤ (12945051905217/100000000000000 : ℝ)^6367
        have hw : |(-1064548551/5000000000 : ℝ)|=(1064548551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266014267/10000000000 : ℝ)|^8415 ≤ (10711106896967/25000000000000 : ℝ)^6367
        have hw : |(5266014267/10000000000 : ℝ)|=(5266014267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392570131/10000000000 : ℝ)|^8415 ≤ (44210520489189/100000000000000 : ℝ)^6367
        have hw : |(5392570131/10000000000 : ℝ)|=(5392570131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s5_5 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312333471/10000000000 : ℝ)*x 0 + (-103336583/500000000 : ℝ)*x 1 + (84258911/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312333471/10000000000 : ℝ)^8415 ≤ (21671601702839/50000000000000 : ℝ)^6367 := by
    have hnat : (5312333471 : ℕ)^8415*50000000000000^6367 ≤ 21671601702839^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312333471 10000000000 21671601702839 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103336583/500000000 : ℝ)^8415 ≤ (48618258657/390625000000 : ℝ)^6367 := by
    have hnat : (103336583 : ℕ)^8415*390625000000^6367 ≤ 48618258657^6367*500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103336583 500000000 48618258657 390625000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84258911/156250000 : ℝ)^8415 ≤ (44210522363731/100000000000000 : ℝ)^6367 := by
    have hnat : (84258911 : ℕ)^8415*100000000000000^6367 ≤ 44210522363731^6367*156250000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84258911 156250000 44210522363731 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312333471/10000000000 : ℝ), (-103336583/500000000 : ℝ), (84258911/156250000 : ℝ)] ![(21671601702839/50000000000000 : ℝ), (48618258657/390625000000 : ℝ), (44210522363731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312333471/10000000000 : ℝ)|^8415 ≤ (21671601702839/50000000000000 : ℝ)^6367
        have hw : |(5312333471/10000000000 : ℝ)|=(5312333471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103336583/500000000 : ℝ)|^8415 ≤ (48618258657/390625000000 : ℝ)^6367
        have hw : |(-103336583/500000000 : ℝ)|=(103336583/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84258911/156250000 : ℝ)|^8415 ≤ (44210522363731/100000000000000 : ℝ)^6367
        have hw : |(84258911/156250000 : ℝ)|=(84258911/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s5_6 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166010419/312500000 : ℝ)*x 0 + (2696285179/5000000000 : ℝ)*x 1 + (-258341459/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166010419/312500000 : ℝ)^8415 ≤ (1733728109053/4000000000000 : ℝ)^6367 := by
    have hnat : (166010419 : ℕ)^8415*4000000000000^6367 ≤ 1733728109053^6367*312500000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166010419 312500000 1733728109053 4000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696285179/5000000000 : ℝ)^8415 ≤ (2763157684303/6250000000000 : ℝ)^6367 := by
    have hnat : (2696285179 : ℕ)^8415*6250000000000^6367 ≤ 2763157684303^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696285179 5000000000 2763157684303 6250000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258341459/1250000000 : ℝ)^8415 ≤ (12446274311703/100000000000000 : ℝ)^6367 := by
    have hnat : (258341459 : ℕ)^8415*100000000000000^6367 ≤ 12446274311703^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258341459 1250000000 12446274311703 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166010419/312500000 : ℝ), (2696285179/5000000000 : ℝ), (-258341459/1250000000 : ℝ)] ![(1733728109053/4000000000000 : ℝ), (2763157684303/6250000000000 : ℝ), (12446274311703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166010419/312500000 : ℝ)|^8415 ≤ (1733728109053/4000000000000 : ℝ)^6367
        have hw : |(166010419/312500000 : ℝ)|=(166010419/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696285179/5000000000 : ℝ)|^8415 ≤ (2763157684303/6250000000000 : ℝ)^6367
        have hw : |(2696285179/5000000000 : ℝ)|=(2696285179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258341459/1250000000 : ℝ)|^8415 ≤ (12446274311703/100000000000000 : ℝ)^6367
        have hw : |(-258341459/1250000000 : ℝ)|=(258341459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s5_7 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353467711/10000000000 : ℝ)*x 0 + (4483180023/10000000000 : ℝ)*x 1 + (1056860853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353467711/10000000000 : ℝ)^8415 ≤ (1665841305861/5000000000000 : ℝ)^6367 := by
    have hnat : (4353467711 : ℕ)^8415*5000000000000^6367 ≤ 1665841305861^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353467711 10000000000 1665841305861 5000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483180023/10000000000 : ℝ)^8415 ≤ (34635055913167/100000000000000 : ℝ)^6367 := by
    have hnat : (4483180023 : ℕ)^8415*100000000000000^6367 ≤ 34635055913167^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483180023 10000000000 34635055913167 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056860853/2500000000 : ℝ)^8415 ≤ (32048117959091/100000000000000 : ℝ)^6367 := by
    have hnat : (1056860853 : ℕ)^8415*100000000000000^6367 ≤ 32048117959091^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056860853 2500000000 32048117959091 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353467711/10000000000 : ℝ), (4483180023/10000000000 : ℝ), (1056860853/2500000000 : ℝ)] ![(1665841305861/5000000000000 : ℝ), (34635055913167/100000000000000 : ℝ), (32048117959091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353467711/10000000000 : ℝ)|^8415 ≤ (1665841305861/5000000000000 : ℝ)^6367
        have hw : |(4353467711/10000000000 : ℝ)|=(4353467711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483180023/10000000000 : ℝ)|^8415 ≤ (34635055913167/100000000000000 : ℝ)^6367
        have hw : |(4483180023/10000000000 : ℝ)|=(4483180023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056860853/2500000000 : ℝ)|^8415 ≤ (32048117959091/100000000000000 : ℝ)^6367
        have hw : |(1056860853/2500000000 : ℝ)|=(1056860853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1222_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11427/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7061/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5659/50000 : ℝ) ^ (4207/1024 : ℝ) ≤ (6478565822424913/50000000000000000000 : ℝ) := by
    have hpowers : (5659/50000 : ℝ)^4207 ≤ (6478565822424913/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5659 : ℕ)^4207*50000000000000000000^1024 ≤ 6478565822424913^1024*50000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5659 50000 6478565822424913 50000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5659/50000 : ℝ)) (X := (6478565822424913/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (4207/1024 : ℝ) ≤ (33249146163309017/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^4207 ≤ (33249146163309017/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3559 : ℕ)^4207*100000000000000000000^1024 ≤ 33249146163309017^1024*25000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 33249146163309017 100000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (33249146163309017/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006478565822424913/25000000000000000000 : ℝ) ≤ (10000630701321019/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (25006478565822424913/25000000000000000000 : ℝ)^1024 ≤ (10000630701321019/10000000000000000 : ℝ)^4207 := by
      have hnat : (25006478565822424913 : ℕ)^1024*10000000000000000^4207 ≤ 10000630701321019^4207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006478565822424913 25000000000000000000 10000630701321019 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000630701321019/10000000000000000 : ℝ)) (X := (25006478565822424913/25000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046206277808158843/100000000000000000000 : ℝ) ≤ (2500281120514207/2500000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (100046206277808158843/100000000000000000000 : ℝ)^1024 ≤ (2500281120514207/2500000000000000 : ℝ)^4207 := by
      have hnat : (100046206277808158843 : ℕ)^1024*2500000000000000^4207 ≤ 2500281120514207^4207*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046206277808158843 100000000000000000000 2500281120514207 2500000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500281120514207/2500000000000000 : ℝ)) (X := (100046206277808158843/100000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033249146163309017/50000000000000000000 : ℝ) ≤ (10001618262792637/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (50033249146163309017/50000000000000000000 : ℝ)^1024 ≤ (10001618262792637/10000000000000000 : ℝ)^4207 := by
      have hnat : (50033249146163309017 : ℕ)^1024*10000000000000000^4207 ≤ 10001618262792637^4207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033249146163309017 50000000000000000000 10001618262792637 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001618262792637/10000000000000000 : ℝ)) (X := (50033249146163309017/50000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6478565822424913/50000000000000000000 : ℝ) ≤ ((14585331582859480459/14590000000000000000 : ℝ)+2*(493780735809/291800000000000 : ℝ)*(5659/50000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (14585331582859480459/14590000000000000000 : ℝ)+2*(493780735809/291800000000000 : ℝ)*(5659/50000 : ℝ)=(10000630701321019/10000000000000000 : ℝ) by norm_num, show 1+2*(6478565822424913/50000000000000000000 : ℝ)=(25006478565822424913/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33249146163309017/100000000000000000000 : ℝ)+(6478565822424913/50000000000000000000 : ℝ) ≤ ((14585331582859480459/14590000000000000000 : ℝ)+(493780735809/291800000000000 : ℝ)*((3559/25000 : ℝ)+(5659/50000 : ℝ)))^(4207/1024 : ℝ) := by
    rw [show (14585331582859480459/14590000000000000000 : ℝ)+(493780735809/291800000000000 : ℝ)*((3559/25000 : ℝ)+(5659/50000 : ℝ))=(2500281120514207/2500000000000000 : ℝ) by norm_num, show 1+(33249146163309017/100000000000000000000 : ℝ)+(6478565822424913/50000000000000000000 : ℝ)=(100046206277808158843/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33249146163309017/100000000000000000000 : ℝ) ≤ ((14585331582859480459/14590000000000000000 : ℝ)+2*(493780735809/291800000000000 : ℝ)*(3559/25000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (14585331582859480459/14590000000000000000 : ℝ)+2*(493780735809/291800000000000 : ℝ)*(3559/25000 : ℝ)=(10001618262792637/10000000000000000 : ℝ) by norm_num, show 1+2*(33249146163309017/100000000000000000000 : ℝ)=(50033249146163309017/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14585331582859480459/14590000000000000000 : ℝ)*(X 1 0+X 2 0)+(493780735809/291800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (14585331582859480459/14590000000000000000 : ℝ)) (alpha := (493780735809/291800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14585331582859480459/14590000000000000000 : ℝ)*(X 0 1+X 2 1)+(493780735809/291800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (14585331582859480459/14590000000000000000 : ℝ)) (alpha := (493780735809/291800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14585331582859480459/14590000000000000000 : ℝ)*(X 0 2+X 1 2)+(493780735809/291800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (14585331582859480459/14590000000000000000 : ℝ)) (alpha := (493780735809/291800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2129092221/10000000000 : ℝ)*X 0 0+(1348224669/2500000000 : ℝ)*X 0 1+(1316421711/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672373773/5000000000 : ℝ)*X 1 0+(-438723027/2000000000 : ℝ)*X 1 1+(5265686859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336186891/2500000000 : ℝ)*X 2 0+(5265686937/10000000000 : ℝ)*X 2 1+(-2193615007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435345733/1000000000 : ℝ)*X 0 0+(1056694981/2500000000 : ℝ)*X 0 1+(70060021/156250000 : ℝ)*X 0 2+(435345733/1000000000 : ℝ)*X 1 0+(1056694981/2500000000 : ℝ)*X 1 1+(70060021/156250000 : ℝ)*X 1 2+(435345733/1000000000 : ℝ)*X 2 0+(1056694981/2500000000 : ℝ)*X 2 1+(70060021/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1064548551/5000000000 : ℝ)*X 0 0+(5266014267/10000000000 : ℝ)*X 0 1+(5392570131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312333471/10000000000 : ℝ)*X 1 0+(-103336583/500000000 : ℝ)*X 1 1+(84258911/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166010419/312500000 : ℝ)*X 2 0+(2696285179/5000000000 : ℝ)*X 2 1+(-258341459/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353467711/10000000000 : ℝ)*X 0 0+(4483180023/10000000000 : ℝ)*X 0 1+(1056860853/2500000000 : ℝ)*X 0 2+(4353467711/10000000000 : ℝ)*X 1 0+(4483180023/10000000000 : ℝ)*X 1 1+(1056860853/2500000000 : ℝ)*X 1 2+(4353467711/10000000000 : ℝ)*X 2 0+(4483180023/10000000000 : ℝ)*X 2 1+(1056860853/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (303225419124805715095515171/36475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1739301983/100000000000000 : ℝ)*(base19) + (175319619/10000000000000 : ℝ)*(base23) + (64290629/100000000000000 : ℝ)*(upper3) + (6723719/100000000000000 : ℝ)*(upper4) + (132723567/50000000000000 : ℝ)*(upper5) + (587559117200523/10000000000000 : ℝ)*(major0) + (587559117200523/10000000000000 : ℝ)*(major1) + (587559117200523/10000000000000 : ℝ)*(major2) + (393047698931217/5000000000000 : ℝ)*(sp0) + (7861012999169667/100000000000000 : ℝ)*(sp1) + (393050649263773/5000000000000 : ℝ)*(sp2) + (3890145950409579/100000000000000 : ℝ)*(sp3) + (6075984731/10000000000000 : ℝ)*(sp4) + (21378021231/100000000000000 : ℝ)*(sp7) + (389016732843081/10000000000000 : ℝ)*(f.failure) + (157220294769433/2000000000000 : ℝ)*(f.sum) + (1329109272599/729500000000000000000000000 : ℝ)*base65 + (3150845145873669943/145900000000000000000000000000000 : ℝ)*base68 + (417392450827769943/145900000000000000000000000000000 : ℝ)*base70 + (1702005140079730057/145900000000000000000000000000000 : ℝ)*base71 + (3247038307069/1459000000000000000000000000 : ℝ)*base74 + (3488649514207469943/145900000000000000000000000000000 : ℝ)*base76 + (481839520362469943/145900000000000000000000000000000 : ℝ)*base78 + (2039046353692669943/145900000000000000000000000000000 : ℝ)*base80 + (1878561993471/291800000000000000000000000 : ℝ)*base81 + (1224609/500000000000000000000 : ℝ)*base89 + (1224609/500000000000000000000 : ℝ)*base91 + (1224609/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1130408122534992747868434909/182375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (276797891/25000000000000 : ℝ)*(base19) + (176774183/12500000000000 : ℝ)*(base23) + (76365381/50000000000000 : ℝ)*(upper3) + (90198259/50000000000000 : ℝ)*(lower4) + (13762727/12500000000000 : ℝ)*(upper5) + (1476489143619839/25000000000000 : ℝ)*(major0) + (1476489143619839/25000000000000 : ℝ)*(major1) + (1476489143619839/25000000000000 : ℝ)*(major2) + (7788224159/20000000000000 : ℝ)*(sp1) + (24479659367/50000000000000 : ℝ)*(sp2) + (7901640999223979/100000000000000 : ℝ)*(sp4) + (395080047545581/5000000000000 : ℝ)*(sp5) + (7901590625711781/100000000000000 : ℝ)*(sp6) + (1955135971562989/50000000000000 : ℝ)*(sp7) + (1955135971562989/50000000000000 : ℝ)*(f.failure) + (7901640999223979/100000000000000 : ℝ)*(f.sum) + (18801863041499/3647500000000000000000000000 : ℝ)*base66 + (2792347737400473899/364750000000000000000000000000000 : ℝ)*base68 + (2146770255595973899/364750000000000000000000000000000 : ℝ)*base70 + (888973746525223899/364750000000000000000000000000000 : ℝ)*base72 + (40232322264353/7295000000000000000000000000 : ℝ)*base74 + (4105220291701973899/364750000000000000000000000000000 : ℝ)*base76 + (1682994933551723899/364750000000000000000000000000000 : ℝ)*base78 + (1177474364654723899/364750000000000000000000000000000 : ℝ)*base80 + (2027146370617/1823750000000000000000000000 : ℝ)*base82 + (2396379/2500000000000000000000 : ℝ)*base90 + (2396379/2500000000000000000000 : ℝ)*base92 + (2396379/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1222_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1222_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1222_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4069/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1222_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1222_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1222_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4069/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1222_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
