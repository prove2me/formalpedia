-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1206_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:05:27.836629+00:00
-- url     : https://prove2.me/submissions/cb393df7-013e-49f3-86e8-263fd9353056

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
theorem support_rectangle_w1206_s6_0 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136629529/10000000000 : ℝ)*x 0 + (5392102867/10000000000 : ℝ)*x 1 + (164577867/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136629529/10000000000 : ℝ)^8399 ≤ (12989359759123/100000000000000 : ℝ)^6351 := by
    have hnat : (2136629529 : ℕ)^8399*100000000000000^6351 ≤ 12989359759123^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136629529 10000000000 12989359759123 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392102867/10000000000 : ℝ)^8399 ≤ (11045834414739/25000000000000 : ℝ)^6351 := by
    have hnat : (5392102867 : ℕ)^8399*25000000000000^6351 ≤ 11045834414739^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392102867 10000000000 11045834414739 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164577867/312500000 : ℝ)^8399 ≤ (21413651283017/50000000000000 : ℝ)^6351 := by
    have hnat : (164577867 : ℕ)^8399*50000000000000^6351 ≤ 21413651283017^6351*312500000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164577867 312500000 21413651283017 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136629529/10000000000 : ℝ), (5392102867/10000000000 : ℝ), (164577867/312500000 : ℝ)] ![(12989359759123/100000000000000 : ℝ), (11045834414739/25000000000000 : ℝ), (21413651283017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136629529/10000000000 : ℝ)|^8399 ≤ (12989359759123/100000000000000 : ℝ)^6351
        have hw : |(-2136629529/10000000000 : ℝ)|=(2136629529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392102867/10000000000 : ℝ)|^8399 ≤ (11045834414739/25000000000000 : ℝ)^6351
        have hw : |(5392102867/10000000000 : ℝ)|=(5392102867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164577867/312500000 : ℝ)|^8399 ≤ (21413651283017/50000000000000 : ℝ)^6351
        have hw : |(164577867/312500000 : ℝ)|=(164577867/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s6_1 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334034323/625000000 : ℝ)*x 0 + (-2200329337/10000000000 : ℝ)*x 1 + (164577867/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334034323/625000000 : ℝ)^8399 ≤ (43668760027341/100000000000000 : ℝ)^6351 := by
    have hnat : (334034323 : ℕ)^8399*100000000000000^6351 ≤ 43668760027341^6351*625000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334034323 625000000 43668760027341 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200329337/10000000000 : ℝ)^8399 ≤ (13503937398849/100000000000000 : ℝ)^6351 := by
    have hnat : (2200329337 : ℕ)^8399*100000000000000^6351 ≤ 13503937398849^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200329337 10000000000 13503937398849 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164577867/312500000 : ℝ)^8399 ≤ (21413651283017/50000000000000 : ℝ)^6351 := by
    have hnat : (164577867 : ℕ)^8399*50000000000000^6351 ≤ 21413651283017^6351*312500000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164577867 312500000 21413651283017 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334034323/625000000 : ℝ), (-2200329337/10000000000 : ℝ), (164577867/312500000 : ℝ)] ![(43668760027341/100000000000000 : ℝ), (13503937398849/100000000000000 : ℝ), (21413651283017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334034323/625000000 : ℝ)|^8399 ≤ (43668760027341/100000000000000 : ℝ)^6351
        have hw : |(334034323/625000000 : ℝ)|=(334034323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2200329337/10000000000 : ℝ)|^8399 ≤ (13503937398849/100000000000000 : ℝ)^6351
        have hw : |(-2200329337/10000000000 : ℝ)|=(2200329337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164577867/312500000 : ℝ)|^8399 ≤ (21413651283017/50000000000000 : ℝ)^6351
        have hw : |(164577867/312500000 : ℝ)|=(164577867/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s6_2 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068909833/2000000000 : ℝ)*x 0 + (5266491743/10000000000 : ℝ)*x 1 + (-2200329341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068909833/2000000000 : ℝ)^8399 ≤ (10917189998731/25000000000000 : ℝ)^6351 := by
    have hnat : (1068909833 : ℕ)^8399*25000000000000^6351 ≤ 10917189998731^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068909833 2000000000 10917189998731 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266491743/10000000000 : ℝ)^8399 ≤ (42827302555279/100000000000000 : ℝ)^6351 := by
    have hnat : (5266491743 : ℕ)^8399*100000000000000^6351 ≤ 42827302555279^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266491743 10000000000 42827302555279 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200329341/10000000000 : ℝ)^8399 ≤ (2700787486263/20000000000000 : ℝ)^6351 := by
    have hnat : (2200329341 : ℕ)^8399*20000000000000^6351 ≤ 2700787486263^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200329341 10000000000 2700787486263 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068909833/2000000000 : ℝ), (5266491743/10000000000 : ℝ), (-2200329341/10000000000 : ℝ)] ![(10917189998731/25000000000000 : ℝ), (42827302555279/100000000000000 : ℝ), (2700787486263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068909833/2000000000 : ℝ)|^8399 ≤ (10917189998731/25000000000000 : ℝ)^6351
        have hw : |(1068909833/2000000000 : ℝ)|=(1068909833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266491743/10000000000 : ℝ)|^8399 ≤ (42827302555279/100000000000000 : ℝ)^6351
        have hw : |(5266491743/10000000000 : ℝ)|=(5266491743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2200329341/10000000000 : ℝ)|^8399 ≤ (2700787486263/20000000000000 : ℝ)^6351
        have hw : |(-2200329341/10000000000 : ℝ)|=(2200329341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s6_3 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87114451/200000000 : ℝ)*x 0 + (846200703/2000000000 : ℝ)*x 1 + (896808897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87114451/200000000 : ℝ)^8399 ≤ (3331718879927/10000000000000 : ℝ)^6351 := by
    have hnat : (87114451 : ℕ)^8399*10000000000000^6351 ≤ 3331718879927^6351*200000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87114451 200000000 3331718879927 10000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846200703/2000000000 : ℝ)^8399 ≤ (2003839864189/6250000000000 : ℝ)^6351 := by
    have hnat : (846200703 : ℕ)^8399*6250000000000^6351 ≤ 2003839864189^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846200703 2000000000 2003839864189 6250000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896808897/2000000000 : ℝ)^8399 ≤ (34621373355903/100000000000000 : ℝ)^6351 := by
    have hnat : (896808897 : ℕ)^8399*100000000000000^6351 ≤ 34621373355903^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896808897 2000000000 34621373355903 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87114451/200000000 : ℝ), (846200703/2000000000 : ℝ), (896808897/2000000000 : ℝ)] ![(3331718879927/10000000000000 : ℝ), (2003839864189/6250000000000 : ℝ), (34621373355903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87114451/200000000 : ℝ)|^8399 ≤ (3331718879927/10000000000000 : ℝ)^6351
        have hw : |(87114451/200000000 : ℝ)|=(87114451/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846200703/2000000000 : ℝ)|^8399 ≤ (2003839864189/6250000000000 : ℝ)^6351
        have hw : |(846200703/2000000000 : ℝ)|=(846200703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896808897/2000000000 : ℝ)|^8399 ≤ (34621373355903/100000000000000 : ℝ)^6351
        have hw : |(896808897/2000000000 : ℝ)|=(896808897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s6_4 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267079293/1250000000 : ℝ)*x 0 + (5266809173/10000000000 : ℝ)*x 1 + (5391784263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267079293/1250000000 : ℝ)^8399 ≤ (6494699235331/50000000000000 : ℝ)^6351 := by
    have hnat : (267079293 : ℕ)^8399*50000000000000^6351 ≤ 6494699235331^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267079293 1250000000 6494699235331 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266809173/10000000000 : ℝ)^8399 ≤ (42830716346617/100000000000000 : ℝ)^6351 := by
    have hnat : (5266809173 : ℕ)^8399*100000000000000^6351 ≤ 42830716346617^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266809173 10000000000 42830716346617 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391784263/10000000000 : ℝ)^8399 ≤ (22089942582583/50000000000000 : ℝ)^6351 := by
    have hnat : (5391784263 : ℕ)^8399*50000000000000^6351 ≤ 22089942582583^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391784263 10000000000 22089942582583 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267079293/1250000000 : ℝ), (5266809173/10000000000 : ℝ), (5391784263/10000000000 : ℝ)] ![(6494699235331/50000000000000 : ℝ), (42830716346617/100000000000000 : ℝ), (22089942582583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267079293/1250000000 : ℝ)|^8399 ≤ (6494699235331/50000000000000 : ℝ)^6351
        have hw : |(-267079293/1250000000 : ℝ)|=(267079293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266809173/10000000000 : ℝ)|^8399 ≤ (42830716346617/100000000000000 : ℝ)^6351
        have hw : |(5266809173/10000000000 : ℝ)|=(5266809173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391784263/10000000000 : ℝ)|^8399 ≤ (22089942582583/50000000000000 : ℝ)^6351
        have hw : |(5391784263/10000000000 : ℝ)|=(5391784263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s6_5 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328144527/2500000000 : ℝ)*x 0 + (-415007371/2000000000 : ℝ)*x 1 + (2695892111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328144527/2500000000 : ℝ)^8399 ≤ (43323630084877/100000000000000 : ℝ)^6351 := by
    have hnat : (1328144527 : ℕ)^8399*100000000000000^6351 ≤ 43323630084877^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328144527 2500000000 43323630084877 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415007371/2000000000 : ℝ)^8399 ≤ (12496485185619/100000000000000 : ℝ)^6351 := by
    have hnat : (415007371 : ℕ)^8399*100000000000000^6351 ≤ 12496485185619^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415007371 2000000000 12496485185619 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695892111/5000000000 : ℝ)^8399 ≤ (22089942360441/50000000000000 : ℝ)^6351 := by
    have hnat : (2695892111 : ℕ)^8399*50000000000000^6351 ≤ 22089942360441^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695892111 5000000000 22089942360441 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328144527/2500000000 : ℝ), (-415007371/2000000000 : ℝ), (2695892111/5000000000 : ℝ)] ![(43323630084877/100000000000000 : ℝ), (12496485185619/100000000000000 : ℝ), (22089942360441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328144527/2500000000 : ℝ)|^8399 ≤ (43323630084877/100000000000000 : ℝ)^6351
        have hw : |(1328144527/2500000000 : ℝ)|=(1328144527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415007371/2000000000 : ℝ)|^8399 ≤ (12496485185619/100000000000000 : ℝ)^6351
        have hw : |(-415007371/2000000000 : ℝ)|=(415007371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695892111/5000000000 : ℝ)|^8399 ≤ (22089942360441/50000000000000 : ℝ)^6351
        have hw : |(2695892111/5000000000 : ℝ)|=(2695892111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s6_6 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265628907/500000000 : ℝ)*x 0 + (5391784219/10000000000 : ℝ)*x 1 + (-415007363/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265628907/500000000 : ℝ)^8399 ≤ (8664726085997/20000000000000 : ℝ)^6351 := by
    have hnat : (265628907 : ℕ)^8399*20000000000000^6351 ≤ 8664726085997^6351*500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265628907 500000000 8664726085997 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391784219/10000000000 : ℝ)^8399 ≤ (44179884688373/100000000000000 : ℝ)^6351 := by
    have hnat : (5391784219 : ℕ)^8399*100000000000000^6351 ≤ 44179884688373^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391784219 10000000000 44179884688373 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415007363/2000000000 : ℝ)^8399 ≤ (12496484867047/100000000000000 : ℝ)^6351 := by
    have hnat : (415007363 : ℕ)^8399*100000000000000^6351 ≤ 12496484867047^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415007363 2000000000 12496484867047 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265628907/500000000 : ℝ), (5391784219/10000000000 : ℝ), (-415007363/2000000000 : ℝ)] ![(8664726085997/20000000000000 : ℝ), (44179884688373/100000000000000 : ℝ), (12496484867047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265628907/500000000 : ℝ)|^8399 ≤ (8664726085997/20000000000000 : ℝ)^6351
        have hw : |(265628907/500000000 : ℝ)|=(265628907/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391784219/10000000000 : ℝ)|^8399 ≤ (44179884688373/100000000000000 : ℝ)^6351
        have hw : |(5391784219/10000000000 : ℝ)|=(5391784219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-415007363/2000000000 : ℝ)|^8399 ≤ (12496484867047/100000000000000 : ℝ)^6351
        have hw : |(-415007363/2000000000 : ℝ)|=(415007363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s6_7 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355732161/10000000000 : ℝ)*x 0 + (2241702519/5000000000 : ℝ)*x 1 + (4231645321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355732161/10000000000 : ℝ)^8399 ≤ (1332691440831/4000000000000 : ℝ)^6351 := by
    have hnat : (4355732161 : ℕ)^8399*4000000000000^6351 ≤ 1332691440831^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355732161 10000000000 1332691440831 4000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241702519/5000000000 : ℝ)^8399 ≤ (34614844239437/100000000000000 : ℝ)^6351 := by
    have hnat : (2241702519 : ℕ)^8399*100000000000000^6351 ≤ 34614844239437^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241702519 5000000000 34614844239437 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231645321/10000000000 : ℝ)^8399 ≤ (16033934864903/50000000000000 : ℝ)^6351 := by
    have hnat : (4231645321 : ℕ)^8399*50000000000000^6351 ≤ 16033934864903^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231645321 10000000000 16033934864903 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355732161/10000000000 : ℝ), (2241702519/5000000000 : ℝ), (4231645321/10000000000 : ℝ)] ![(1332691440831/4000000000000 : ℝ), (34614844239437/100000000000000 : ℝ), (16033934864903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355732161/10000000000 : ℝ)|^8399 ≤ (1332691440831/4000000000000 : ℝ)^6351
        have hw : |(4355732161/10000000000 : ℝ)|=(4355732161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241702519/5000000000 : ℝ)|^8399 ≤ (34614844239437/100000000000000 : ℝ)^6351
        have hw : |(2241702519/5000000000 : ℝ)|=(2241702519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231645321/10000000000 : ℝ)|^8399 ≤ (16033934864903/50000000000000 : ℝ)^6351
        have hw : |(4231645321/10000000000 : ℝ)|=(4231645321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1206_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1143/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1409/10000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5703/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5703/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5703/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5703/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5703/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5703/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5703/50000 : ℝ) ^ (4199/1024 : ℝ) ≤ (1360486838751657/10000000000000000000 : ℝ) := by
    have hpowers : (5703/50000 : ℝ)^4199 ≤ (1360486838751657/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5703 : ℕ)^4199*10000000000000000000^1024 ≤ 1360486838751657^1024*50000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5703 50000 1360486838751657 10000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5703/50000 : ℝ)) (X := (1360486838751657/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2823/20000 : ℝ) ^ (4199/1024 : ℝ) ≤ (32598182313296933/100000000000000000000 : ℝ) := by
    have hpowers : (2823/20000 : ℝ)^4199 ≤ (32598182313296933/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2823 : ℕ)^4199*100000000000000000000^1024 ≤ 32598182313296933^1024*20000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 20000 32598182313296933 100000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/20000 : ℝ)) (X := (32598182313296933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001360486838751657/5000000000000000000 : ℝ) ≤ (1000066348903663/1000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (5001360486838751657/5000000000000000000 : ℝ)^1024 ≤ (1000066348903663/1000000000000000 : ℝ)^4199 := by
      have hnat : (5001360486838751657 : ℕ)^1024*1000000000000000^4199 ≤ 1000066348903663^4199*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001360486838751657 5000000000000000000 1000066348903663 1000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000066348903663/1000000000000000 : ℝ)) (X := (5001360486838751657/5000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046203050700813503/100000000000000000000 : ℝ) ≤ (10001126545886977/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (100046203050700813503/100000000000000000000 : ℝ)^1024 ≤ (10001126545886977/10000000000000000 : ℝ)^4199 := by
      have hnat : (100046203050700813503 : ℕ)^1024*10000000000000000^4199 ≤ 10001126545886977^4199*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046203050700813503 100000000000000000000 10001126545886977 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001126545886977/10000000000000000 : ℝ)) (X := (100046203050700813503/100000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032598182313296933/50000000000000000000 : ℝ) ≤ (2500397400684331/2500000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (50032598182313296933/50000000000000000000 : ℝ)^1024 ≤ (2500397400684331/2500000000000000 : ℝ)^4199 := by
      have hnat : (50032598182313296933 : ℕ)^1024*2500000000000000^4199 ≤ 2500397400684331^4199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032598182313296933 50000000000000000000 2500397400684331 2500000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500397400684331/2500000000000000 : ℝ)) (X := (50032598182313296933/50000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1360486838751657/10000000000000000000 : ℝ) ≤ ((214930429674048531/215000000000000000 : ℝ)+2*(22050326207/12900000000000 : ℝ)*(5703/50000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (214930429674048531/215000000000000000 : ℝ)+2*(22050326207/12900000000000 : ℝ)*(5703/50000 : ℝ)=(1000066348903663/1000000000000000 : ℝ) by norm_num, show 1+2*(1360486838751657/10000000000000000000 : ℝ)=(5001360486838751657/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32598182313296933/100000000000000000000 : ℝ)+(1360486838751657/10000000000000000000 : ℝ) ≤ ((214930429674048531/215000000000000000 : ℝ)+(22050326207/12900000000000 : ℝ)*((2823/20000 : ℝ)+(5703/50000 : ℝ)))^(4199/1024 : ℝ) := by
    rw [show (214930429674048531/215000000000000000 : ℝ)+(22050326207/12900000000000 : ℝ)*((2823/20000 : ℝ)+(5703/50000 : ℝ))=(10001126545886977/10000000000000000 : ℝ) by norm_num, show 1+(32598182313296933/100000000000000000000 : ℝ)+(1360486838751657/10000000000000000000 : ℝ)=(100046203050700813503/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32598182313296933/100000000000000000000 : ℝ) ≤ ((214930429674048531/215000000000000000 : ℝ)+2*(22050326207/12900000000000 : ℝ)*(2823/20000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (214930429674048531/215000000000000000 : ℝ)+2*(22050326207/12900000000000 : ℝ)*(2823/20000 : ℝ)=(2500397400684331/2500000000000000 : ℝ) by norm_num, show 1+2*(32598182313296933/100000000000000000000 : ℝ)=(50032598182313296933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (214930429674048531/215000000000000000 : ℝ)*(X 1 0+X 2 0)+(22050326207/12900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (5703/50000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (214930429674048531/215000000000000000 : ℝ)) (alpha := (22050326207/12900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (214930429674048531/215000000000000000 : ℝ)*(X 0 1+X 2 1)+(22050326207/12900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (5703/50000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (214930429674048531/215000000000000000 : ℝ)) (alpha := (22050326207/12900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (214930429674048531/215000000000000000 : ℝ)*(X 0 2+X 1 2)+(22050326207/12900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (5703/50000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (214930429674048531/215000000000000000 : ℝ)) (alpha := (22050326207/12900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2136629529/10000000000 : ℝ)*X 0 0+(5392102867/10000000000 : ℝ)*X 0 1+(164577867/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334034323/625000000 : ℝ)*X 1 0+(-2200329337/10000000000 : ℝ)*X 1 1+(164577867/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068909833/2000000000 : ℝ)*X 2 0+(5266491743/10000000000 : ℝ)*X 2 1+(-2200329341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((87114451/200000000 : ℝ)*X 0 0+(846200703/2000000000 : ℝ)*X 0 1+(896808897/2000000000 : ℝ)*X 0 2+(87114451/200000000 : ℝ)*X 1 0+(846200703/2000000000 : ℝ)*X 1 1+(896808897/2000000000 : ℝ)*X 1 2+(87114451/200000000 : ℝ)*X 2 0+(846200703/2000000000 : ℝ)*X 2 1+(896808897/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-267079293/1250000000 : ℝ)*X 0 0+(5266809173/10000000000 : ℝ)*X 0 1+(5391784263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328144527/2500000000 : ℝ)*X 1 0+(-415007371/2000000000 : ℝ)*X 1 1+(2695892111/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265628907/500000000 : ℝ)*X 2 0+(5391784219/10000000000 : ℝ)*X 2 1+(-415007363/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355732161/10000000000 : ℝ)*X 0 0+(2241702519/5000000000 : ℝ)*X 0 1+(4231645321/10000000000 : ℝ)*X 0 2+(4355732161/10000000000 : ℝ)*X 1 0+(2241702519/5000000000 : ℝ)*X 1 1+(4231645321/10000000000 : ℝ)*X 1 2+(4355732161/10000000000 : ℝ)*X 2 0+(2241702519/5000000000 : ℝ)*X 2 1+(4231645321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1321450522849180839030251/671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38120769/10000000000000 : ℝ)*(base19) + (352550703/100000000000000 : ℝ)*(base23) + (12927539/100000000000000 : ℝ)*(lower2) + (5180013/10000000000000 : ℝ)*(upper3) + (25746309/100000000000000 : ℝ)*(upper5) + (93070623840521/1562500000000 : ℝ)*(major0) + (93070623840521/1562500000000 : ℝ)*(major1) + (93070623840521/1562500000000 : ℝ)*(major2) + (7961089561457491/100000000000000 : ℝ)*(sp0) + (7961099447809737/100000000000000 : ℝ)*(sp1) + (1990274869116681/25000000000000 : ℝ)*(sp2) + (1975967120205757/50000000000000 : ℝ)*(sp3) + (5013457/48828125000 : ℝ)*(sp4) + (1143319481/20000000000000 : ℝ)*(sp7) + (1975969978504459/50000000000000 : ℝ)*(f.failure) + (7961099829017427/100000000000000 : ℝ)*(f.sum) + (2043296328091/322500000000000000000000000 : ℝ)*base66 + (16377889082694781/2015625000000000000000000000000 : ℝ)*base67 + (17799275498038531/2015625000000000000000000000000 : ℝ)*base69 + (6453728190492719/2015625000000000000000000000000 : ℝ)*base72 + (531129840287/645000000000000000000000000 : ℝ)*base74 + (18805536257038531/2015625000000000000000000000000 : ℝ)*base75 + (18542366698944781/2015625000000000000000000000000 : ℝ)*base77 + (8603719544448953/1007812500000000000000000000000 : ℝ)*base79 + (985209633887/645000000000000000000000000 : ℝ)*base82 + (978967/1250000000000000000000 : ℝ)*base90 + (978967/1250000000000000000000 : ℝ)*base92 + (978967/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (932947778322232651743777/430000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28922661/6250000000000 : ℝ)*(base19) + (576527763/100000000000000 : ℝ)*(base23) + (20872297/100000000000000 : ℝ)*(upper2) + (25655389/50000000000000 : ℝ)*(upper3) + (2716809/6250000000000 : ℝ)*(upper5) + (239472721007911/4000000000000 : ℝ)*(major0) + (239472721007911/4000000000000 : ℝ)*(major1) + (239472721007911/4000000000000 : ℝ)*(major2) + (10306577613/100000000000000 : ℝ)*(sp1) + (229272383/1562500000000 : ℝ)*(sp2) + (160031886108819/2000000000000 : ℝ)*(sp4) + (4000791768050381/50000000000000 : ℝ)*(sp5) + (2000394763870169/25000000000000 : ℝ)*(sp6) + (1986020836316527/50000000000000 : ℝ)*(sp7) + (1986020836316527/50000000000000 : ℝ)*(f.failure) + (160031886108819/2000000000000 : ℝ)*(f.sum) + (79396595441/129000000000000000000000000 : ℝ)*base66 + (32834652088476223/2580000000000000000000000000000 : ℝ)*base67 + (28184073650916223/2580000000000000000000000000000 : ℝ)*base69 + (34658496472716223/2580000000000000000000000000000 : ℝ)*base71 + (176600208229/32250000000000000000000000 : ℝ)*base73 + (8523481064963777/2580000000000000000000000000000 : ℝ)*base76 + (50567857905516223/2580000000000000000000000000000 : ℝ)*base77 + (47047736475323777/2580000000000000000000000000000 : ℝ)*base80 + (95593307573/129000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5727851/1250000000000000000000 : ℝ)*base90 + (5727851/1250000000000000000000 : ℝ)*base92 + (5727851/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1206_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1206_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1206_s7_0 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136649507/10000000000 : ℝ)*x 0 + (1347966457/2500000000 : ℝ)*x 1 + (5266715653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136649507/10000000000 : ℝ)^8399 ≤ (1623690047253/12500000000000 : ℝ)^6351 := by
    have hnat : (2136649507 : ℕ)^8399*12500000000000^6351 ≤ 1623690047253^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136649507 10000000000 1623690047253 12500000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347966457/2500000000 : ℝ)^8399 ≤ (44180769023059/100000000000000 : ℝ)^6351 := by
    have hnat : (1347966457 : ℕ)^8399*100000000000000^6351 ≤ 44180769023059^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347966457 2500000000 44180769023059 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266715653/10000000000 : ℝ)^8399 ≤ (4282971058171/10000000000000 : ℝ)^6351 := by
    have hnat : (5266715653 : ℕ)^8399*10000000000000^6351 ≤ 4282971058171^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266715653 10000000000 4282971058171 10000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136649507/10000000000 : ℝ), (1347966457/2500000000 : ℝ), (5266715653/10000000000 : ℝ)] ![(1623690047253/12500000000000 : ℝ), (44180769023059/100000000000000 : ℝ), (4282971058171/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136649507/10000000000 : ℝ)|^8399 ≤ (1623690047253/12500000000000 : ℝ)^6351
        have hw : |(-2136649507/10000000000 : ℝ)|=(2136649507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347966457/2500000000 : ℝ)|^8399 ≤ (44180769023059/100000000000000 : ℝ)^6351
        have hw : |(1347966457/2500000000 : ℝ)|=(1347966457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266715653/10000000000 : ℝ)|^8399 ≤ (4282971058171/10000000000000 : ℝ)^6351
        have hw : |(5266715653/10000000000 : ℝ)|=(5266715653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s7_1 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344489343/10000000000 : ℝ)*x 0 + (-550028077/2500000000 : ℝ)*x 1 + (131667891/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344489343/10000000000 : ℝ)^8399 ≤ (21834056794449/50000000000000 : ℝ)^6351 := by
    have hnat : (5344489343 : ℕ)^8399*50000000000000^6351 ≤ 21834056794449^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344489343 10000000000 21834056794449 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550028077/2500000000 : ℝ)^8399 ≤ (13502175953969/100000000000000 : ℝ)^6351 := by
    have hnat : (550028077 : ℕ)^8399*100000000000000^6351 ≤ 13502175953969^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550028077 2500000000 13502175953969 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131667891/250000000 : ℝ)^8399 ≤ (42829710441901/100000000000000 : ℝ)^6351 := by
    have hnat : (131667891 : ℕ)^8399*100000000000000^6351 ≤ 42829710441901^6351*250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131667891 250000000 42829710441901 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344489343/10000000000 : ℝ), (-550028077/2500000000 : ℝ), (131667891/250000000 : ℝ)] ![(21834056794449/50000000000000 : ℝ), (13502175953969/100000000000000 : ℝ), (42829710441901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344489343/10000000000 : ℝ)|^8399 ≤ (21834056794449/50000000000000 : ℝ)^6351
        have hw : |(5344489343/10000000000 : ℝ)|=(5344489343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-550028077/2500000000 : ℝ)|^8399 ≤ (13502175953969/100000000000000 : ℝ)^6351
        have hw : |(-550028077/2500000000 : ℝ)|=(550028077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131667891/250000000 : ℝ)|^8399 ≤ (42829710441901/100000000000000 : ℝ)^6351
        have hw : |(131667891/250000000 : ℝ)|=(131667891/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s7_2 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344489333/10000000000 : ℝ)*x 0 + (2633357823/5000000000 : ℝ)*x 1 + (-2200112313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344489333/10000000000 : ℝ)^8399 ≤ (43668113480843/100000000000000 : ℝ)^6351 := by
    have hnat : (5344489333 : ℕ)^8399*100000000000000^6351 ≤ 43668113480843^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344489333 10000000000 43668113480843 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633357823/5000000000 : ℝ)^8399 ≤ (10707427626607/25000000000000 : ℝ)^6351 := by
    have hnat : (2633357823 : ℕ)^8399*25000000000000^6351 ≤ 10707427626607^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633357823 5000000000 10707427626607 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200112313/10000000000 : ℝ)^8399 ≤ (13502175994549/100000000000000 : ℝ)^6351 := by
    have hnat : (2200112313 : ℕ)^8399*100000000000000^6351 ≤ 13502175994549^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200112313 10000000000 13502175994549 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344489333/10000000000 : ℝ), (2633357823/5000000000 : ℝ), (-2200112313/10000000000 : ℝ)] ![(43668113480843/100000000000000 : ℝ), (10707427626607/25000000000000 : ℝ), (13502175994549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344489333/10000000000 : ℝ)|^8399 ≤ (43668113480843/100000000000000 : ℝ)^6351
        have hw : |(5344489333/10000000000 : ℝ)|=(5344489333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633357823/5000000000 : ℝ)|^8399 ≤ (10707427626607/25000000000000 : ℝ)^6351
        have hw : |(2633357823/5000000000 : ℝ)|=(2633357823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2200112313/10000000000 : ℝ)|^8399 ≤ (13502175994549/100000000000000 : ℝ)^6351
        have hw : |(-2200112313/10000000000 : ℝ)|=(2200112313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s7_3 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355734249/10000000000 : ℝ)*x 0 + (2115733131/5000000000 : ℝ)*x 1 + (4483578719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355734249/10000000000 : ℝ)^8399 ≤ (1665865357113/5000000000000 : ℝ)^6351 := by
    have hnat : (4355734249 : ℕ)^8399*5000000000000^6351 ≤ 1665865357113^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355734249 10000000000 1665865357113 5000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115733131/5000000000 : ℝ)^8399 ≤ (16033037623067/50000000000000 : ℝ)^6351 := by
    have hnat : (2115733131 : ℕ)^8399*50000000000000^6351 ≤ 16033037623067^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115733131 5000000000 16033037623067 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483578719/10000000000 : ℝ)^8399 ≤ (3461661759123/10000000000000 : ℝ)^6351 := by
    have hnat : (4483578719 : ℕ)^8399*10000000000000^6351 ≤ 3461661759123^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483578719 10000000000 3461661759123 10000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355734249/10000000000 : ℝ), (2115733131/5000000000 : ℝ), (4483578719/10000000000 : ℝ)] ![(1665865357113/5000000000000 : ℝ), (16033037623067/50000000000000 : ℝ), (3461661759123/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355734249/10000000000 : ℝ)|^8399 ≤ (1665865357113/5000000000000 : ℝ)^6351
        have hw : |(4355734249/10000000000 : ℝ)|=(4355734249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115733131/5000000000 : ℝ)|^8399 ≤ (16033037623067/50000000000000 : ℝ)^6351
        have hw : |(2115733131/5000000000 : ℝ)|=(2115733131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483578719/10000000000 : ℝ)|^8399 ≤ (3461661759123/10000000000000 : ℝ)^6351
        have hw : |(4483578719/10000000000 : ℝ)|=(4483578719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s7_4 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-427330853/2000000000 : ℝ)*x 0 + (6583789/12500000 : ℝ)*x 1 + (2695774563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427330853/2000000000 : ℝ)^8399 ≤ (12989558631411/100000000000000 : ℝ)^6351 := by
    have hnat : (427330853 : ℕ)^8399*100000000000000^6351 ≤ 12989558631411^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427330853 2000000000 12989558631411 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6583789/12500000 : ℝ)^8399 ≤ (42833104168709/100000000000000 : ℝ)^6351 := by
    have hnat : (6583789 : ℕ)^8399*100000000000000^6351 ≤ 42833104168709^6351*12500000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6583789 12500000 42833104168709 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695774563/5000000000 : ℝ)^8399 ≤ (110443342971/250000000000 : ℝ)^6351 := by
    have hnat : (2695774563 : ℕ)^8399*250000000000^6351 ≤ 110443342971^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695774563 5000000000 110443342971 250000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427330853/2000000000 : ℝ), (6583789/12500000 : ℝ), (2695774563/5000000000 : ℝ)] ![(12989558631411/100000000000000 : ℝ), (42833104168709/100000000000000 : ℝ), (110443342971/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427330853/2000000000 : ℝ)|^8399 ≤ (12989558631411/100000000000000 : ℝ)^6351
        have hw : |(-427330853/2000000000 : ℝ)|=(427330853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6583789/12500000 : ℝ)|^8399 ≤ (42833104168709/100000000000000 : ℝ)^6351
        have hw : |(6583789/12500000 : ℝ)|=(6583789/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695774563/5000000000 : ℝ)|^8399 ≤ (110443342971/250000000000 : ℝ)^6351
        have hw : |(2695774563/5000000000 : ℝ)|=(2695774563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s7_5 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312635503/10000000000 : ℝ)*x 0 + (-1037639139/5000000000 : ℝ)*x 1 + (673943707/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312635503/10000000000 : ℝ)^8399 ≤ (43324249069409/100000000000000 : ℝ)^6351 := by
    have hnat : (5312635503 : ℕ)^8399*100000000000000^6351 ≤ 43324249069409^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312635503 10000000000 43324249069409 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037639139/5000000000 : ℝ)^8399 ≤ (624920399327/5000000000000 : ℝ)^6351 := by
    have hnat : (1037639139 : ℕ)^8399*5000000000000^6351 ≤ 624920399327^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037639139 5000000000 624920399327 5000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673943707/1250000000 : ℝ)^8399 ≤ (5522167866439/12500000000000 : ℝ)^6351 := by
    have hnat : (673943707 : ℕ)^8399*12500000000000^6351 ≤ 5522167866439^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673943707 1250000000 5522167866439 12500000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312635503/10000000000 : ℝ), (-1037639139/5000000000 : ℝ), (673943707/1250000000 : ℝ)] ![(43324249069409/100000000000000 : ℝ), (624920399327/5000000000000 : ℝ), (5522167866439/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312635503/10000000000 : ℝ)|^8399 ≤ (43324249069409/100000000000000 : ℝ)^6351
        have hw : |(5312635503/10000000000 : ℝ)|=(5312635503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1037639139/5000000000 : ℝ)|^8399 ≤ (624920399327/5000000000000 : ℝ)^6351
        have hw : |(-1037639139/5000000000 : ℝ)|=(1037639139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673943707/1250000000 : ℝ)|^8399 ≤ (5522167866439/12500000000000 : ℝ)^6351
        have hw : |(673943707/1250000000 : ℝ)|=(673943707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s7_6 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312635789/10000000000 : ℝ)*x 0 + (1347887293/2500000000 : ℝ)*x 1 + (-2075278549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312635789/10000000000 : ℝ)^8399 ≤ (21662126076911/50000000000000 : ℝ)^6351 := by
    have hnat : (5312635789 : ℕ)^8399*50000000000000^6351 ≤ 21662126076911^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312635789 10000000000 21662126076911 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347887293/2500000000 : ℝ)^8399 ≤ (44177337686859/100000000000000 : ℝ)^6351 := by
    have hnat : (1347887293 : ℕ)^8399*100000000000000^6351 ≤ 44177337686859^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347887293 2500000000 44177337686859 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2075278549/10000000000 : ℝ)^8399 ≤ (6249205072473/50000000000000 : ℝ)^6351 := by
    have hnat : (2075278549 : ℕ)^8399*50000000000000^6351 ≤ 6249205072473^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075278549 10000000000 6249205072473 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312635789/10000000000 : ℝ), (1347887293/2500000000 : ℝ), (-2075278549/10000000000 : ℝ)] ![(21662126076911/50000000000000 : ℝ), (44177337686859/100000000000000 : ℝ), (6249205072473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312635789/10000000000 : ℝ)|^8399 ≤ (21662126076911/50000000000000 : ℝ)^6351
        have hw : |(5312635789/10000000000 : ℝ)|=(5312635789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347887293/2500000000 : ℝ)|^8399 ≤ (44177337686859/100000000000000 : ℝ)^6351
        have hw : |(1347887293/2500000000 : ℝ)|=(1347887293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2075278549/10000000000 : ℝ)|^8399 ≤ (6249205072473/50000000000000 : ℝ)^6351
        have hw : |(-2075278549/10000000000 : ℝ)|=(2075278549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s7_7 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871148723/2000000000 : ℝ)*x 0 + (4482944149/10000000000 : ℝ)*x 1 + (2116051651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871148723/2000000000 : ℝ)^8399 ≤ (33317401885513/100000000000000 : ℝ)^6351 := by
    have hnat : (871148723 : ℕ)^8399*100000000000000^6351 ≤ 33317401885513^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871148723 2000000000 33317401885513 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482944149/10000000000 : ℝ)^8399 ≤ (17305069243807/50000000000000 : ℝ)^6351 := by
    have hnat : (4482944149 : ℕ)^8399*50000000000000^6351 ≤ 17305069243807^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482944149 10000000000 17305069243807 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116051651/5000000000 : ℝ)^8399 ≤ (6414491922019/20000000000000 : ℝ)^6351 := by
    have hnat : (2116051651 : ℕ)^8399*20000000000000^6351 ≤ 6414491922019^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116051651 5000000000 6414491922019 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871148723/2000000000 : ℝ), (4482944149/10000000000 : ℝ), (2116051651/5000000000 : ℝ)] ![(33317401885513/100000000000000 : ℝ), (17305069243807/50000000000000 : ℝ), (6414491922019/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871148723/2000000000 : ℝ)|^8399 ≤ (33317401885513/100000000000000 : ℝ)^6351
        have hw : |(871148723/2000000000 : ℝ)|=(871148723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482944149/10000000000 : ℝ)|^8399 ≤ (17305069243807/50000000000000 : ℝ)^6351
        have hw : |(4482944149/10000000000 : ℝ)|=(4482944149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116051651/5000000000 : ℝ)|^8399 ≤ (6414491922019/20000000000000 : ℝ)^6351
        have hw : |(2116051651/5000000000 : ℝ)|=(2116051651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1206_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5717/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2817/20000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (1143/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1143/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1143/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1143/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1143/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1143/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1143/10000 : ℝ) ^ (4199/1024 : ℝ) ≤ (13722638369052819/100000000000000000000 : ℝ) := by
    have hpowers : (1143/10000 : ℝ)^4199 ≤ (13722638369052819/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1143 : ℕ)^4199*100000000000000000000^1024 ≤ 13722638369052819^1024*10000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1143 10000 13722638369052819 100000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1143/10000 : ℝ)) (X := (13722638369052819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1409/10000 : ℝ) ^ (4199/1024 : ℝ) ≤ (505657453012463/1562500000000000000 : ℝ) := by
    have hpowers : (1409/10000 : ℝ)^4199 ≤ (505657453012463/1562500000000000000 : ℝ)^1024 := by
      have hnat : (1409 : ℕ)^4199*1562500000000000000^1024 ≤ 505657453012463^1024*10000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 10000 505657453012463 1562500000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/10000 : ℝ)) (X := (505657453012463/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013722638369052819/50000000000000000000 : ℝ) ≤ (1250083653988283/1250000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (50013722638369052819/50000000000000000000 : ℝ)^1024 ≤ (1250083653988283/1250000000000000 : ℝ)^4199 := by
      have hnat : (50013722638369052819 : ℕ)^1024*1250000000000000^4199 ≤ 1250083653988283^4199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013722638369052819 50000000000000000000 1250083653988283 1250000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250083653988283/1250000000000000 : ℝ)) (X := (50013722638369052819/50000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046084715361850451/100000000000000000000 : ℝ) ≤ (10001123661078093/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (100046084715361850451/100000000000000000000 : ℝ)^1024 ≤ (10001123661078093/10000000000000000 : ℝ)^4199 := by
      have hnat : (100046084715361850451 : ℕ)^1024*10000000000000000^4199 ≤ 10001123661078093^4199*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046084715361850451 100000000000000000000 10001123661078093 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001123661078093/10000000000000000 : ℝ)) (X := (100046084715361850451/100000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781755657453012463/781250000000000000 : ℝ) ≤ (5000789045124961/5000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (781755657453012463/781250000000000000 : ℝ)^1024 ≤ (5000789045124961/5000000000000000 : ℝ)^4199 := by
      have hnat : (781755657453012463 : ℕ)^1024*5000000000000000^4199 ≤ 5000789045124961^4199*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781755657453012463 781250000000000000 5000789045124961 5000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000789045124961/5000000000000000 : ℝ)) (X := (781755657453012463/781250000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13722638369052819/100000000000000000000 : ℝ) ≤ ((265913919060026513/266000000000000000 : ℝ)+2*(454429171829/266000000000000 : ℝ)*(1143/10000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (265913919060026513/266000000000000000 : ℝ)+2*(454429171829/266000000000000 : ℝ)*(1143/10000 : ℝ)=(1250083653988283/1250000000000000 : ℝ) by norm_num, show 1+2*(13722638369052819/100000000000000000000 : ℝ)=(50013722638369052819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(505657453012463/1562500000000000000 : ℝ)+(13722638369052819/100000000000000000000 : ℝ) ≤ ((265913919060026513/266000000000000000 : ℝ)+(454429171829/266000000000000 : ℝ)*((1409/10000 : ℝ)+(1143/10000 : ℝ)))^(4199/1024 : ℝ) := by
    rw [show (265913919060026513/266000000000000000 : ℝ)+(454429171829/266000000000000 : ℝ)*((1409/10000 : ℝ)+(1143/10000 : ℝ))=(10001123661078093/10000000000000000 : ℝ) by norm_num, show 1+(505657453012463/1562500000000000000 : ℝ)+(13722638369052819/100000000000000000000 : ℝ)=(100046084715361850451/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(505657453012463/1562500000000000000 : ℝ) ≤ ((265913919060026513/266000000000000000 : ℝ)+2*(454429171829/266000000000000 : ℝ)*(1409/10000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (265913919060026513/266000000000000000 : ℝ)+2*(454429171829/266000000000000 : ℝ)*(1409/10000 : ℝ)=(5000789045124961/5000000000000000 : ℝ) by norm_num, show 1+2*(505657453012463/1562500000000000000 : ℝ)=(781755657453012463/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (265913919060026513/266000000000000000 : ℝ)*(X 1 0+X 2 0)+(454429171829/266000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (1143/10000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (265913919060026513/266000000000000000 : ℝ)) (alpha := (454429171829/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (265913919060026513/266000000000000000 : ℝ)*(X 0 1+X 2 1)+(454429171829/266000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (1143/10000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (265913919060026513/266000000000000000 : ℝ)) (alpha := (454429171829/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (265913919060026513/266000000000000000 : ℝ)*(X 0 2+X 1 2)+(454429171829/266000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (1143/10000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (265913919060026513/266000000000000000 : ℝ)) (alpha := (454429171829/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2136649507/10000000000 : ℝ)*X 0 0+(1347966457/2500000000 : ℝ)*X 0 1+(5266715653/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344489343/10000000000 : ℝ)*X 1 0+(-550028077/2500000000 : ℝ)*X 1 1+(131667891/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344489333/10000000000 : ℝ)*X 2 0+(2633357823/5000000000 : ℝ)*X 2 1+(-2200112313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355734249/10000000000 : ℝ)*X 0 0+(2115733131/5000000000 : ℝ)*X 0 1+(4483578719/10000000000 : ℝ)*X 0 2+(4355734249/10000000000 : ℝ)*X 1 0+(2115733131/5000000000 : ℝ)*X 1 1+(4483578719/10000000000 : ℝ)*X 1 2+(4355734249/10000000000 : ℝ)*X 2 0+(2115733131/5000000000 : ℝ)*X 2 1+(4483578719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-427330853/2000000000 : ℝ)*X 0 0+(6583789/12500000 : ℝ)*X 0 1+(2695774563/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312635503/10000000000 : ℝ)*X 1 0+(-1037639139/5000000000 : ℝ)*X 1 1+(673943707/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312635789/10000000000 : ℝ)*X 2 0+(1347887293/2500000000 : ℝ)*X 2 1+(-2075278549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871148723/2000000000 : ℝ)*X 0 0+(4482944149/10000000000 : ℝ)*X 0 1+(2116051651/5000000000 : ℝ)*X 0 2+(871148723/2000000000 : ℝ)*X 1 0+(4482944149/10000000000 : ℝ)*X 1 1+(2116051651/5000000000 : ℝ)*X 1 2+(871148723/2000000000 : ℝ)*X 2 0+(4482944149/10000000000 : ℝ)*X 2 1+(2116051651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3835796843756071405244037/415625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1803186333/100000000000000 : ℝ)*(base19) + (207581227/12500000000000 : ℝ)*(base23) + (68187993/100000000000000 : ℝ)*(lower2) + (48488829/20000000000000 : ℝ)*(upper3) + (34352951/25000000000000 : ℝ)*(upper5) + (46707165546199/781250000000 : ℝ)*(major0) + (46707165546199/781250000000 : ℝ)*(major1) + (46707165546199/781250000000 : ℝ)*(major2) + (7990451592200633/100000000000000 : ℝ)*(sp0) + (7990497906523133/100000000000000 : ℝ)*(sp1) + (159809960981193/2000000000000 : ℝ)*(sp2) + (793301535748807/20000000000000 : ℝ)*(sp3) + (24058754417/50000000000000 : ℝ)*(sp4) + (133418703/500000000000 : ℝ)*(sp7) + (1983267181242317/50000000000000 : ℝ)*(f.failure) + (3995249854854733/50000000000000 : ℝ)*(f.sum) + (1601936660761/1662500000000000000000000000 : ℝ)*base65 + (931151181683/195312500000000000000000000 : ℝ)*base67 + (1465054978991/390625000000000000000000000 : ℝ)*base69 + (2021060464759/390625000000000000000000000 : ℝ)*base72 + (1592681802561/1662500000000000000000000000 : ℝ)*base73 + (84203837685053/3125000000000000000000000000 : ℝ)*base75 + (28818260560053/3125000000000000000000000000 : ℝ)*base77 + (11668554716491/390625000000000000000000000 : ℝ)*base79 + (18324747372303/3325000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (9273121/1250000000000000000000 : ℝ)*base90 + (9273121/1250000000000000000000 : ℝ)*base92 + (9273121/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9378746700977403847731987/6650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63009359/20000000000000 : ℝ)*(base19) + (412010757/50000000000000 : ℝ)*(base23) + (37383069/50000000000000 : ℝ)*(upper2) + (2850247/25000000000000 : ℝ)*(upper3) + (3004399592434833/50000000000000 : ℝ)*(major0) + (3004399592434833/50000000000000 : ℝ)*(major1) + (3004399592434833/50000000000000 : ℝ)*(major2) + (11203443291/25000000000000 : ℝ)*(sp1) + (6824788727/20000000000000 : ℝ)*(sp2) + (8114075759/50000000000000 : ℝ)*(sp3) + (1606194585870037/20000000000000 : ℝ)*(sp4) + (4015463900265113/50000000000000 : ℝ)*(sp5) + (2007734495346259/25000000000000 : ℝ)*(sp6) + (3986609165226359/100000000000000 : ℝ)*(sp7) + (3986625393377877/100000000000000 : ℝ)*(f.failure) + (1606194585870037/20000000000000 : ℝ)*(f.sum) + (6994835285257/6650000000000000000000000000 : ℝ)*base65 + (938651480667787/100000000000000000000000000000 : ℝ)*base68 + (841740476967787/100000000000000000000000000000 : ℝ)*base70 + (1993347370332213/100000000000000000000000000000 : ℝ)*base71 + (2041402404007/6650000000000000000000000000 : ℝ)*base73 + (1559170367567787/100000000000000000000000000000 : ℝ)*base76 + (22967977432213/100000000000000000000000000000 : ℝ)*base77 + (1720134620867787/100000000000000000000000000000 : ℝ)*base80 + (23679710148093/6650000000000000000000000000 : ℝ)*base82 + (19324599/2500000000000000000000 : ℝ)*base89 + (19324599/2500000000000000000000 : ℝ)*base91 + (19324599/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1206_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1206_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1206_s8_0 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-106832783/500000000 : ℝ)*x 0 + (336988841/625000000 : ℝ)*x 1 + (2633377881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106832783/500000000 : ℝ)^8399 ≤ (6494784923471/50000000000000 : ℝ)^6351 := by
    have hnat : (106832783 : ℕ)^8399*50000000000000^6351 ≤ 6494784923471^6351*500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106832783 500000000 6494784923471 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336988841/625000000 : ℝ)^8399 ≤ (8836057639379/20000000000000 : ℝ)^6351 := by
    have hnat : (336988841 : ℕ)^8399*20000000000000^6351 ≤ 8836057639379^6351*625000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336988841 625000000 8836057639379 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633377881/5000000000 : ℝ)^8399 ≤ (42830141934989/100000000000000 : ℝ)^6351 := by
    have hnat : (2633377881 : ℕ)^8399*100000000000000^6351 ≤ 42830141934989^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633377881 5000000000 42830141934989 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106832783/500000000 : ℝ), (336988841/625000000 : ℝ), (2633377881/5000000000 : ℝ)] ![(6494784923471/50000000000000 : ℝ), (8836057639379/20000000000000 : ℝ), (42830141934989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106832783/500000000 : ℝ)|^8399 ≤ (6494784923471/50000000000000 : ℝ)^6351
        have hw : |(-106832783/500000000 : ℝ)|=(106832783/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336988841/625000000 : ℝ)|^8399 ≤ (8836057639379/20000000000000 : ℝ)^6351
        have hw : |(336988841/625000000 : ℝ)|=(336988841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633377881/5000000000 : ℝ)|^8399 ≤ (42830141934989/100000000000000 : ℝ)^6351
        have hw : |(2633377881/5000000000 : ℝ)|=(2633377881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s8_1 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344477431/10000000000 : ℝ)*x 0 + (-2200075031/10000000000 : ℝ)*x 1 + (263337787/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344477431/10000000000 : ℝ)^8399 ≤ (43667984874179/100000000000000 : ℝ)^6351 := by
    have hnat : (5344477431 : ℕ)^8399*100000000000000^6351 ≤ 43667984874179^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344477431 10000000000 43667984874179 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200075031/10000000000 : ℝ)^8399 ≤ (13501873413031/100000000000000 : ℝ)^6351 := by
    have hnat : (2200075031 : ℕ)^8399*100000000000000^6351 ≤ 13501873413031^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200075031 10000000000 13501873413031 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263337787/500000000 : ℝ)^8399 ≤ (42830141698389/100000000000000 : ℝ)^6351 := by
    have hnat : (263337787 : ℕ)^8399*100000000000000^6351 ≤ 42830141698389^6351*500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263337787 500000000 42830141698389 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344477431/10000000000 : ℝ), (-2200075031/10000000000 : ℝ), (263337787/500000000 : ℝ)] ![(43667984874179/100000000000000 : ℝ), (13501873413031/100000000000000 : ℝ), (42830141698389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344477431/10000000000 : ℝ)|^8399 ≤ (43667984874179/100000000000000 : ℝ)^6351
        have hw : |(5344477431/10000000000 : ℝ)|=(5344477431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2200075031/10000000000 : ℝ)|^8399 ≤ (13501873413031/100000000000000 : ℝ)^6351
        have hw : |(-2200075031/10000000000 : ℝ)|=(2200075031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263337787/500000000 : ℝ)|^8399 ≤ (42830141698389/100000000000000 : ℝ)^6351
        have hw : |(263337787/500000000 : ℝ)|=(263337787/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s8_2 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344477413/10000000000 : ℝ)*x 0 + (1316688943/2500000000 : ℝ)*x 1 + (-550018753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344477413/10000000000 : ℝ)^8399 ≤ (34115613031/78125000000 : ℝ)^6351 := by
    have hnat : (5344477413 : ℕ)^8399*78125000000^6351 ≤ 34115613031^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344477413 10000000000 34115613031 78125000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316688943/2500000000 : ℝ)^8399 ≤ (8566028408507/20000000000000 : ℝ)^6351 := by
    have hnat : (1316688943 : ℕ)^8399*20000000000000^6351 ≤ 8566028408507^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316688943 2500000000 8566028408507 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550018753/2500000000 : ℝ)^8399 ≤ (13501873258827/100000000000000 : ℝ)^6351 := by
    have hnat : (550018753 : ℕ)^8399*100000000000000^6351 ≤ 13501873258827^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550018753 2500000000 13501873258827 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344477413/10000000000 : ℝ), (1316688943/2500000000 : ℝ), (-550018753/2500000000 : ℝ)] ![(34115613031/78125000000 : ℝ), (8566028408507/20000000000000 : ℝ), (13501873258827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344477413/10000000000 : ℝ)|^8399 ≤ (34115613031/78125000000 : ℝ)^6351
        have hw : |(5344477413/10000000000 : ℝ)|=(5344477413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316688943/2500000000 : ℝ)|^8399 ≤ (8566028408507/20000000000000 : ℝ)^6351
        have hw : |(1316688943/2500000000 : ℝ)|=(1316688943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550018753/2500000000 : ℝ)|^8399 ≤ (13501873258827/100000000000000 : ℝ)^6351
        have hw : |(-550018753/2500000000 : ℝ)|=(550018753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s8_3 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177868189/5000000000 : ℝ)*x 0 + (2115775549/5000000000 : ℝ)*x 1 + (2241746671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177868189/5000000000 : ℝ)^8399 ≤ (3331732867849/10000000000000 : ℝ)^6351 := by
    have hnat : (2177868189 : ℕ)^8399*10000000000000^6351 ≤ 3331732867849^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177868189 5000000000 3331732867849 10000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115775549/5000000000 : ℝ)^8399 ≤ (2004182840491/6250000000000 : ℝ)^6351 := by
    have hnat : (2115775549 : ℕ)^8399*6250000000000^6351 ≤ 2004182840491^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115775549 5000000000 2004182840491 6250000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241746671/5000000000 : ℝ)^8399 ≤ (865393646387/2500000000000 : ℝ)^6351 := by
    have hnat : (2241746671 : ℕ)^8399*2500000000000^6351 ≤ 865393646387^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241746671 5000000000 865393646387 2500000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177868189/5000000000 : ℝ), (2115775549/5000000000 : ℝ), (2241746671/5000000000 : ℝ)] ![(3331732867849/10000000000000 : ℝ), (2004182840491/6250000000000 : ℝ), (865393646387/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177868189/5000000000 : ℝ)|^8399 ≤ (3331732867849/10000000000000 : ℝ)^6351
        have hw : |(2177868189/5000000000 : ℝ)|=(2177868189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115775549/5000000000 : ℝ)|^8399 ≤ (2004182840491/6250000000000 : ℝ)^6351
        have hw : |(2115775549/5000000000 : ℝ)|=(2115775549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241746671/5000000000 : ℝ)|^8399 ≤ (865393646387/2500000000000 : ℝ)^6351
        have hw : |(2241746671/5000000000 : ℝ)|=(2241746671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s8_4 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136660389/10000000000 : ℝ)*x 0 + (658383813/1250000000 : ℝ)*x 1 + (5391505573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136660389/10000000000 : ℝ)^8399 ≤ (1298960786721/10000000000000 : ℝ)^6351 := by
    have hnat : (2136660389 : ℕ)^8399*10000000000000^6351 ≤ 1298960786721^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136660389 10000000000 1298960786721 10000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658383813/1250000000 : ℝ)^8399 ≤ (42833526872751/100000000000000 : ℝ)^6351 := by
    have hnat : (658383813 : ℕ)^8399*100000000000000^6351 ≤ 42833526872751^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658383813 1250000000 42833526872751 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391505573/10000000000 : ℝ)^8399 ≤ (8835373049211/20000000000000 : ℝ)^6351 := by
    have hnat : (5391505573 : ℕ)^8399*20000000000000^6351 ≤ 8835373049211^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391505573 10000000000 8835373049211 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136660389/10000000000 : ℝ), (658383813/1250000000 : ℝ), (5391505573/10000000000 : ℝ)] ![(1298960786721/10000000000000 : ℝ), (42833526872751/100000000000000 : ℝ), (8835373049211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136660389/10000000000 : ℝ)|^8399 ≤ (1298960786721/10000000000000 : ℝ)^6351
        have hw : |(-2136660389/10000000000 : ℝ)|=(2136660389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658383813/1250000000 : ℝ)|^8399 ≤ (42833526872751/100000000000000 : ℝ)^6351
        have hw : |(658383813/1250000000 : ℝ)|=(658383813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391505573/10000000000 : ℝ)|^8399 ≤ (8835373049211/20000000000000 : ℝ)^6351
        have hw : |(5391505573/10000000000 : ℝ)|=(5391505573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s8_5 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355745897/10000000000 : ℝ)*x 0 + (4482859283/10000000000 : ℝ)*x 1 + (846437491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355745897/10000000000 : ℝ)^8399 ≤ (16658712484727/50000000000000 : ℝ)^6351 := by
    have hnat : (4355745897 : ℕ)^8399*50000000000000^6351 ≤ 16658712484727^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355745897 10000000000 16658712484727 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482859283/10000000000 : ℝ)^8399 ≤ (34609272008927/100000000000000 : ℝ)^6351 := by
    have hnat : (4482859283 : ℕ)^8399*100000000000000^6351 ≤ 34609272008927^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482859283 10000000000 34609272008927 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846437491/2000000000 : ℝ)^8399 ≤ (32073303007909/100000000000000 : ℝ)^6351 := by
    have hnat : (846437491 : ℕ)^8399*100000000000000^6351 ≤ 32073303007909^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846437491 2000000000 32073303007909 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355745897/10000000000 : ℝ), (4482859283/10000000000 : ℝ), (846437491/2000000000 : ℝ)] ![(16658712484727/50000000000000 : ℝ), (34609272008927/100000000000000 : ℝ), (32073303007909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355745897/10000000000 : ℝ)|^8399 ≤ (16658712484727/50000000000000 : ℝ)^6351
        have hw : |(4355745897/10000000000 : ℝ)|=(4355745897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482859283/10000000000 : ℝ)|^8399 ≤ (34609272008927/100000000000000 : ℝ)^6351
        have hw : |(4482859283/10000000000 : ℝ)|=(4482859283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846437491/2000000000 : ℝ)|^8399 ≤ (32073303007909/100000000000000 : ℝ)^6351
        have hw : |(846437491/2000000000 : ℝ)|=(846437491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1206_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2287/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2817/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5717/50000 : ℝ) ^ (4199/1024 : ℝ) ≤ (13742341394178719/100000000000000000000 : ℝ) := by
    have hpowers : (5717/50000 : ℝ)^4199 ≤ (13742341394178719/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5717 : ℕ)^4199*100000000000000000000^1024 ≤ 13742341394178719^1024*50000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5717 50000 13742341394178719 100000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5717/50000 : ℝ)) (X := (13742341394178719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2817/20000 : ℝ) ^ (4199/1024 : ℝ) ≤ (32315011524186993/100000000000000000000 : ℝ) := by
    have hpowers : (2817/20000 : ℝ)^4199 ≤ (32315011524186993/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2817 : ℕ)^4199*100000000000000000000^1024 ≤ 32315011524186993^1024*20000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 20000 32315011524186993 100000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/20000 : ℝ)) (X := (32315011524186993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013742341394178719/50000000000000000000 : ℝ) ≤ (10000670192692583/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (50013742341394178719/50000000000000000000 : ℝ)^1024 ≤ (10000670192692583/10000000000000000 : ℝ)^4199 := by
      have hnat : (50013742341394178719 : ℕ)^1024*10000000000000000^4199 ≤ 10000670192692583^4199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013742341394178719 50000000000000000000 10000670192692583 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000670192692583/10000000000000000 : ℝ)) (X := (50013742341394178719/50000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252878584557397857/6250000000000000000 : ℝ) ≤ (10001122994029143/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (6252878584557397857/6250000000000000000 : ℝ)^1024 ≤ (10001122994029143/10000000000000000 : ℝ)^4199 := by
      have hnat : (6252878584557397857 : ℕ)^1024*10000000000000000^4199 ≤ 10001122994029143^4199*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252878584557397857 6250000000000000000 10001122994029143 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001122994029143/10000000000000000 : ℝ)) (X := (6252878584557397857/6250000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032315011524186993/50000000000000000000 : ℝ) ≤ (10001575795365703/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (50032315011524186993/50000000000000000000 : ℝ)^1024 ≤ (10001575795365703/10000000000000000 : ℝ)^4199 := by
      have hnat : (50032315011524186993 : ℕ)^1024*10000000000000000^4199 ≤ 10001575795365703^4199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032315011524186993 50000000000000000000 10001575795365703 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001575795365703/10000000000000000 : ℝ)) (X := (50032315011524186993/50000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13742341394178719/100000000000000000000 : ℝ) ≤ ((26501422019863583453/26510000000000000000 : ℝ)+2*(5660016707/3313750000000 : ℝ)*(5717/50000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (26501422019863583453/26510000000000000000 : ℝ)+2*(5660016707/3313750000000 : ℝ)*(5717/50000 : ℝ)=(10000670192692583/10000000000000000 : ℝ) by norm_num, show 1+2*(13742341394178719/100000000000000000000 : ℝ)=(50013742341394178719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32315011524186993/100000000000000000000 : ℝ)+(13742341394178719/100000000000000000000 : ℝ) ≤ ((26501422019863583453/26510000000000000000 : ℝ)+(5660016707/3313750000000 : ℝ)*((2817/20000 : ℝ)+(5717/50000 : ℝ)))^(4199/1024 : ℝ) := by
    rw [show (26501422019863583453/26510000000000000000 : ℝ)+(5660016707/3313750000000 : ℝ)*((2817/20000 : ℝ)+(5717/50000 : ℝ))=(10001122994029143/10000000000000000 : ℝ) by norm_num, show 1+(32315011524186993/100000000000000000000 : ℝ)+(13742341394178719/100000000000000000000 : ℝ)=(6252878584557397857/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32315011524186993/100000000000000000000 : ℝ) ≤ ((26501422019863583453/26510000000000000000 : ℝ)+2*(5660016707/3313750000000 : ℝ)*(2817/20000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (26501422019863583453/26510000000000000000 : ℝ)+2*(5660016707/3313750000000 : ℝ)*(2817/20000 : ℝ)=(10001575795365703/10000000000000000 : ℝ) by norm_num, show 1+2*(32315011524186993/100000000000000000000 : ℝ)=(50032315011524186993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26501422019863583453/26510000000000000000 : ℝ)*(X 1 0+X 2 0)+(5660016707/3313750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (26501422019863583453/26510000000000000000 : ℝ)) (alpha := (5660016707/3313750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26501422019863583453/26510000000000000000 : ℝ)*(X 0 1+X 2 1)+(5660016707/3313750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (26501422019863583453/26510000000000000000 : ℝ)) (alpha := (5660016707/3313750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26501422019863583453/26510000000000000000 : ℝ)*(X 0 2+X 1 2)+(5660016707/3313750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (26501422019863583453/26510000000000000000 : ℝ)) (alpha := (5660016707/3313750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-106832783/500000000 : ℝ)*X 0 0+(336988841/625000000 : ℝ)*X 0 1+(2633377881/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344477431/10000000000 : ℝ)*X 1 0+(-2200075031/10000000000 : ℝ)*X 1 1+(263337787/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344477413/10000000000 : ℝ)*X 2 0+(1316688943/2500000000 : ℝ)*X 2 1+(-550018753/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177868189/5000000000 : ℝ)*X 0 0+(2115775549/5000000000 : ℝ)*X 0 1+(2241746671/5000000000 : ℝ)*X 0 2+(2177868189/5000000000 : ℝ)*X 1 0+(2115775549/5000000000 : ℝ)*X 1 1+(2241746671/5000000000 : ℝ)*X 1 2+(2177868189/5000000000 : ℝ)*X 2 0+(2115775549/5000000000 : ℝ)*X 2 1+(2241746671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2136660389/10000000000 : ℝ)*X 0 0+(658383813/1250000000 : ℝ)*X 0 1+(5391505573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4355745897/10000000000 : ℝ)*X 0 0+(4482859283/10000000000 : ℝ)*X 0 1+(846437491/2000000000 : ℝ)*X 0 2+(4355745897/10000000000 : ℝ)*X 1 0+(4482859283/10000000000 : ℝ)*X 1 1+(846437491/2000000000 : ℝ)*X 1 2+(4355745897/10000000000 : ℝ)*X 2 0+(4482859283/10000000000 : ℝ)*X 2 1+(846437491/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5235007612728469108239942897/662750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (386705507/25000000000000 : ℝ)*(base19) + (1409126847/100000000000000 : ℝ)*(base23) + (5919829/10000000000000 : ℝ)*(lower2) + (46900983/25000000000000 : ℝ)*(upper3) + (6591351/5000000000000 : ℝ)*(upper5) + (2991272608760983/50000000000000 : ℝ)*(major0) + (2991272608760983/50000000000000 : ℝ)*(major1) + (2991272608760983/50000000000000 : ℝ)*(major2) + (7995841114791961/100000000000000 : ℝ)*(sp0) + (7995881808817377/100000000000000 : ℝ)*(sp1) + (7995881946512559/100000000000000 : ℝ)*(sp2) + (496148046953339/12500000000000 : ℝ)*(sp3) + (8448169489/20000000000000 : ℝ)*(sp4) + (22440480551/100000000000000 : ℝ)*(sp5) + (1984603408053631/50000000000000 : ℝ)*(f.failure) + (1599176671127881/20000000000000 : ℝ)*(f.sum) + (2351901847663/1325500000000000000000000000 : ℝ)*base66 + (106712148102607791/120500000000000000000000000000000 : ℝ)*base68 + (557980704258107791/120500000000000000000000000000000 : ℝ)*base70 + (1057961400235107791/120500000000000000000000000000000 : ℝ)*base72 + (102381964607/265100000000000000000000000 : ℝ)*base73 + (533971773325392209/120500000000000000000000000000000 : ℝ)*base75 + (3169026371525107791/120500000000000000000000000000000 : ℝ)*base78 + (1150782104131392209/120500000000000000000000000000000 : ℝ)*base79 + (9012495534241/2651000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (9986203/1250000000000000000000 : ℝ)*base90 + (9986203/1250000000000000000000 : ℝ)*base92 + (9986203/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1206_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2287/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1206_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1206_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2287/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1206_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1206_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1206_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2287/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1206_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
