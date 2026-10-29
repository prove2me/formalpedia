-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1327_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:46:03.936236+00:00
-- url     : https://prove2.me/submissions/e25585d7-6023-448e-b694-7e44f8111675

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
theorem support_rectangle_w1327_s3_0 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411015839/2000000000 : ℝ)*x 0 + (5429134313/10000000000 : ℝ)*x 1 + (5229743859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411015839/2000000000 : ℝ)^4287 ≤ (6253876517703/50000000000000 : ℝ)^3263 := by
    have hnat : (411015839 : ℕ)^4287*50000000000000^3263 ≤ 6253876517703^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411015839 2000000000 6253876517703 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429134313/10000000000 : ℝ)^4287 ≤ (11205295473099/25000000000000 : ℝ)^3263 := by
    have hnat : (5429134313 : ℕ)^4287*25000000000000^3263 ≤ 11205295473099^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429134313 10000000000 11205295473099 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229743859/10000000000 : ℝ)^4287 ≤ (5333883132527/12500000000000 : ℝ)^3263 := by
    have hnat : (5229743859 : ℕ)^4287*12500000000000^3263 ≤ 5333883132527^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229743859 10000000000 5333883132527 12500000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411015839/2000000000 : ℝ), (5429134313/10000000000 : ℝ), (5229743859/10000000000 : ℝ)] ![(6253876517703/50000000000000 : ℝ), (11205295473099/25000000000000 : ℝ), (5333883132527/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411015839/2000000000 : ℝ)|^4287 ≤ (6253876517703/50000000000000 : ℝ)^3263
        have hw : |(-411015839/2000000000 : ℝ)|=(411015839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429134313/10000000000 : ℝ)|^4287 ≤ (11205295473099/25000000000000 : ℝ)^3263
        have hw : |(5429134313/10000000000 : ℝ)|=(5429134313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229743859/10000000000 : ℝ)|^4287 ≤ (5333883132527/12500000000000 : ℝ)^3263
        have hw : |(5229743859/10000000000 : ℝ)|=(5229743859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s3_1 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353234033/10000000000 : ℝ)*x 0 + (-1078511147/5000000000 : ℝ)*x 1 + (326858999/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353234033/10000000000 : ℝ)^4287 ≤ (21999871083299/50000000000000 : ℝ)^3263 := by
    have hnat : (5353234033 : ℕ)^4287*50000000000000^3263 ≤ 21999871083299^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353234033 10000000000 21999871083299 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078511147/5000000000 : ℝ)^4287 ≤ (6664595708689/50000000000000 : ℝ)^3263 := by
    have hnat : (1078511147 : ℕ)^4287*50000000000000^3263 ≤ 6664595708689^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078511147 5000000000 6664595708689 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326858999/625000000 : ℝ)^4287 ≤ (213355332001/500000000000 : ℝ)^3263 := by
    have hnat : (326858999 : ℕ)^4287*500000000000^3263 ≤ 213355332001^3263*625000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326858999 625000000 213355332001 500000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353234033/10000000000 : ℝ), (-1078511147/5000000000 : ℝ), (326858999/625000000 : ℝ)] ![(21999871083299/50000000000000 : ℝ), (6664595708689/50000000000000 : ℝ), (213355332001/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353234033/10000000000 : ℝ)|^4287 ≤ (21999871083299/50000000000000 : ℝ)^3263
        have hw : |(5353234033/10000000000 : ℝ)|=(5353234033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1078511147/5000000000 : ℝ)|^4287 ≤ (6664595708689/50000000000000 : ℝ)^3263
        have hw : |(-1078511147/5000000000 : ℝ)|=(1078511147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326858999/625000000 : ℝ)|^4287 ≤ (213355332001/500000000000 : ℝ)^3263
        have hw : |(326858999/625000000 : ℝ)|=(326858999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s3_2 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353233801/10000000000 : ℝ)*x 0 + (1307436053/2500000000 : ℝ)*x 1 + (-1078511151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353233801/10000000000 : ℝ)^4287 ≤ (21999869830653/50000000000000 : ℝ)^3263 := by
    have hnat : (5353233801 : ℕ)^4287*50000000000000^3263 ≤ 21999869830653^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353233801 10000000000 21999869830653 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307436053/2500000000 : ℝ)^4287 ≤ (4267106884433/10000000000000 : ℝ)^3263 := by
    have hnat : (1307436053 : ℕ)^4287*10000000000000^3263 ≤ 4267106884433^3263*2500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307436053 2500000000 4267106884433 10000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078511151/5000000000 : ℝ)^4287 ≤ (1666148935291/12500000000000 : ℝ)^3263 := by
    have hnat : (1078511151 : ℕ)^4287*12500000000000^3263 ≤ 1666148935291^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078511151 5000000000 1666148935291 12500000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353233801/10000000000 : ℝ), (1307436053/2500000000 : ℝ), (-1078511151/5000000000 : ℝ)] ![(21999869830653/50000000000000 : ℝ), (4267106884433/10000000000000 : ℝ), (1666148935291/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353233801/10000000000 : ℝ)|^4287 ≤ (21999869830653/50000000000000 : ℝ)^3263
        have hw : |(5353233801/10000000000 : ℝ)|=(5353233801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1307436053/2500000000 : ℝ)|^4287 ≤ (4267106884433/10000000000000 : ℝ)^3263
        have hw : |(1307436053/2500000000 : ℝ)|=(1307436053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1078511151/5000000000 : ℝ)|^4287 ≤ (1666148935291/12500000000000 : ℝ)^3263
        have hw : |(-1078511151/5000000000 : ℝ)|=(1078511151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s3_3 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4329396423/10000000000 : ℝ)*x 0 + (4126437923/10000000000 : ℝ)*x 1 + (4541719753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329396423/10000000000 : ℝ)^4287 ≤ (33291272163443/100000000000000 : ℝ)^3263 := by
    have hnat : (4329396423 : ℕ)^4287*100000000000000^3263 ≤ 33291272163443^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329396423 10000000000 33291272163443 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4126437923/10000000000 : ℝ)^4287 ≤ (15628040822739/50000000000000 : ℝ)^3263 := by
    have hnat : (4126437923 : ℕ)^4287*50000000000000^3263 ≤ 15628040822739^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126437923 10000000000 15628040822739 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4541719753/10000000000 : ℝ)^4287 ≤ (4431580771913/12500000000000 : ℝ)^3263 := by
    have hnat : (4541719753 : ℕ)^4287*12500000000000^3263 ≤ 4431580771913^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541719753 10000000000 4431580771913 12500000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329396423/10000000000 : ℝ), (4126437923/10000000000 : ℝ), (4541719753/10000000000 : ℝ)] ![(33291272163443/100000000000000 : ℝ), (15628040822739/50000000000000 : ℝ), (4431580771913/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329396423/10000000000 : ℝ)|^4287 ≤ (33291272163443/100000000000000 : ℝ)^3263
        have hw : |(4329396423/10000000000 : ℝ)|=(4329396423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4126437923/10000000000 : ℝ)|^4287 ≤ (15628040822739/50000000000000 : ℝ)^3263
        have hw : |(4126437923/10000000000 : ℝ)|=(4126437923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4541719753/10000000000 : ℝ)|^4287 ≤ (4431580771913/12500000000000 : ℝ)^3263
        have hw : |(4541719753/10000000000 : ℝ)|=(4541719753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s3_4 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1027549693/5000000000 : ℝ)*x 0 + (5230582473/10000000000 : ℝ)*x 1 + (2714145281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027549693/5000000000 : ℝ)^4287 ≤ (12507914488229/100000000000000 : ℝ)^3263 := by
    have hnat : (1027549693 : ℕ)^4287*100000000000000^3263 ≤ 12507914488229^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027549693 5000000000 12507914488229 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230582473/10000000000 : ℝ)^4287 ≤ (42680055118539/100000000000000 : ℝ)^3263 := by
    have hnat : (5230582473 : ℕ)^4287*100000000000000^3263 ≤ 42680055118539^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230582473 10000000000 42680055118539 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714145281/5000000000 : ℝ)^4287 ≤ (44812030380733/100000000000000 : ℝ)^3263 := by
    have hnat : (2714145281 : ℕ)^4287*100000000000000^3263 ≤ 44812030380733^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714145281 5000000000 44812030380733 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1027549693/5000000000 : ℝ), (5230582473/10000000000 : ℝ), (2714145281/5000000000 : ℝ)] ![(12507914488229/100000000000000 : ℝ), (42680055118539/100000000000000 : ℝ), (44812030380733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1027549693/5000000000 : ℝ)|^4287 ≤ (12507914488229/100000000000000 : ℝ)^3263
        have hw : |(-1027549693/5000000000 : ℝ)|=(1027549693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230582473/10000000000 : ℝ)|^4287 ≤ (42680055118539/100000000000000 : ℝ)^3263
        have hw : |(5230582473/10000000000 : ℝ)|=(5230582473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714145281/5000000000 : ℝ)|^4287 ≤ (44812030380733/100000000000000 : ℝ)^3263
        have hw : |(2714145281/5000000000 : ℝ)|=(2714145281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s3_5 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060392639/2000000000 : ℝ)*x 0 + (-97923799/500000000 : ℝ)*x 1 + (135707269/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060392639/2000000000 : ℝ)^4287 ≤ (1086172978267/2500000000000 : ℝ)^3263 := by
    have hnat : (1060392639 : ℕ)^4287*2500000000000^3263 ≤ 1086172978267^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060392639 2000000000 1086172978267 2500000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97923799/500000000 : ℝ)^4287 ≤ (2348209665693/20000000000000 : ℝ)^3263 := by
    have hnat : (97923799 : ℕ)^4287*20000000000000^3263 ≤ 2348209665693^3263*500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97923799 500000000 2348209665693 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135707269/250000000 : ℝ)^4287 ≤ (44812032528233/100000000000000 : ℝ)^3263 := by
    have hnat : (135707269 : ℕ)^4287*100000000000000^3263 ≤ 44812032528233^3263*250000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135707269 250000000 44812032528233 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060392639/2000000000 : ℝ), (-97923799/500000000 : ℝ), (135707269/250000000 : ℝ)] ![(1086172978267/2500000000000 : ℝ), (2348209665693/20000000000000 : ℝ), (44812032528233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060392639/2000000000 : ℝ)|^4287 ≤ (1086172978267/2500000000000 : ℝ)^3263
        have hw : |(1060392639/2000000000 : ℝ)|=(1060392639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97923799/500000000 : ℝ)|^4287 ≤ (2348209665693/20000000000000 : ℝ)^3263
        have hw : |(-97923799/500000000 : ℝ)|=(97923799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135707269/250000000 : ℝ)|^4287 ≤ (44812032528233/100000000000000 : ℝ)^3263
        have hw : |(135707269/250000000 : ℝ)|=(135707269/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s3_6 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060392979/2000000000 : ℝ)*x 0 + (169634049/312500000 : ℝ)*x 1 + (-979237649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060392979/2000000000 : ℝ)^4287 ≤ (43446937433063/100000000000000 : ℝ)^3263 := by
    have hnat : (1060392979 : ℕ)^4287*100000000000000^3263 ≤ 43446937433063^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060392979 2000000000 43446937433063 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169634049/312500000 : ℝ)^4287 ≤ (896240391997/2000000000000 : ℝ)^3263 := by
    have hnat : (169634049 : ℕ)^4287*2000000000000^3263 ≤ 896240391997^3263*312500000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169634049 312500000 896240391997 2000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979237649/5000000000 : ℝ)^4287 ≤ (5870521478397/50000000000000 : ℝ)^3263 := by
    have hnat : (979237649 : ℕ)^4287*50000000000000^3263 ≤ 5870521478397^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979237649 5000000000 5870521478397 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060392979/2000000000 : ℝ), (169634049/312500000 : ℝ), (-979237649/5000000000 : ℝ)] ![(43446937433063/100000000000000 : ℝ), (896240391997/2000000000000 : ℝ), (5870521478397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060392979/2000000000 : ℝ)|^4287 ≤ (43446937433063/100000000000000 : ℝ)^3263
        have hw : |(1060392979/2000000000 : ℝ)|=(1060392979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169634049/312500000 : ℝ)|^4287 ≤ (896240391997/2000000000000 : ℝ)^3263
        have hw : |(169634049/312500000 : ℝ)|=(169634049/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979237649/5000000000 : ℝ)|^4287 ≤ (5870521478397/50000000000000 : ℝ)^3263
        have hw : |(-979237649/5000000000 : ℝ)|=(979237649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s3_7 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4329439109/10000000000 : ℝ)*x 0 + (4539973123/10000000000 : ℝ)*x 1 + (258012147/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329439109/10000000000 : ℝ)^4287 ≤ (16645851704969/50000000000000 : ℝ)^3263 := by
    have hnat : (4329439109 : ℕ)^4287*50000000000000^3263 ≤ 16645851704969^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329439109 10000000000 16645851704969 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4539973123/10000000000 : ℝ)^4287 ≤ (35434734366753/100000000000000 : ℝ)^3263 := by
    have hnat : (4539973123 : ℕ)^4287*100000000000000^3263 ≤ 35434734366753^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539973123 10000000000 35434734366753 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258012147/625000000 : ℝ)^4287 ≤ (7818390550227/25000000000000 : ℝ)^3263 := by
    have hnat : (258012147 : ℕ)^4287*25000000000000^3263 ≤ 7818390550227^3263*625000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258012147 625000000 7818390550227 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329439109/10000000000 : ℝ), (4539973123/10000000000 : ℝ), (258012147/625000000 : ℝ)] ![(16645851704969/50000000000000 : ℝ), (35434734366753/100000000000000 : ℝ), (7818390550227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329439109/10000000000 : ℝ)|^4287 ≤ (16645851704969/50000000000000 : ℝ)^3263
        have hw : |(4329439109/10000000000 : ℝ)|=(4329439109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4539973123/10000000000 : ℝ)|^4287 ≤ (35434734366753/100000000000000 : ℝ)^3263
        have hw : |(4539973123/10000000000 : ℝ)|=(4539973123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258012147/625000000 : ℝ)|^4287 ≤ (7818390550227/25000000000000 : ℝ)^3263
        have hw : |(258012147/625000000 : ℝ)|=(258012147/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1327_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3233/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1219/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5403/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (601/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3233/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1219/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3233/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1219/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3233/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1219/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3233/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1219/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3233/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1219/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3233/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1219/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1219/12500 : ℝ) ^ (2143/512 : ℝ) ≤ (1468061579246551/25000000000000000000 : ℝ) := by
    have hpowers : (1219/12500 : ℝ)^2143 ≤ (1468061579246551/25000000000000000000 : ℝ)^512 := by
      have hnat : (1219 : ℕ)^2143*25000000000000000000^512 ≤ 1468061579246551^512*12500^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1219 12500 1468061579246551 25000000000000000000 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1219/12500 : ℝ)) (X := (1468061579246551/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3233/20000 : ℝ) ^ (2143/512 : ℝ) ≤ (24345939369272343/50000000000000000000 : ℝ) := by
    have hpowers : (3233/20000 : ℝ)^2143 ≤ (24345939369272343/50000000000000000000 : ℝ)^512 := by
      have hnat : (3233 : ℕ)^2143*50000000000000000000^512 ≤ 24345939369272343^512*20000^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3233 20000 24345939369272343 50000000000000000000 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3233/20000 : ℝ)) (X := (24345939369272343/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501468061579246551/12500000000000000000 : ℝ) ≤ (10000280583831181/10000000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (12501468061579246551/12500000000000000000 : ℝ)^512 ≤ (10000280583831181/10000000000000000 : ℝ)^2143 := by
      have hnat : (12501468061579246551 : ℕ)^512*10000000000000000^2143 ≤ 10000280583831181^2143*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501468061579246551 12500000000000000000 10000280583831181 10000000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000280583831181/10000000000000000 : ℝ)) (X := (12501468061579246551/12500000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005456412505553089/10000000000000000000 : ℝ) ≤ (10001303361321003/10000000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (10005456412505553089/10000000000000000000 : ℝ)^512 ≤ (10001303361321003/10000000000000000 : ℝ)^2143 := by
      have hnat : (10005456412505553089 : ℕ)^512*10000000000000000^2143 ≤ 10001303361321003^2143*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005456412505553089 10000000000000000000 10001303361321003 10000000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001303361321003/10000000000000000 : ℝ)) (X := (10005456412505553089/10000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25024345939369272343/25000000000000000000 : ℝ) ≤ (400093045552433/400000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (25024345939369272343/25000000000000000000 : ℝ)^512 ≤ (400093045552433/400000000000000 : ℝ)^2143 := by
      have hnat : (25024345939369272343 : ℕ)^512*400000000000000^2143 ≤ 400093045552433^2143*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25024345939369272343 25000000000000000000 400093045552433 400000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400093045552433/400000000000000 : ℝ)) (X := (25024345939369272343/25000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1468061579246551/25000000000000000000 : ℝ) ≤ ((21993773973223971/22000000000000000 : ℝ)+2*(46489885901/29150000000000 : ℝ)*(1219/12500 : ℝ))^(2143/512 : ℝ) := by
    rw [show (21993773973223971/22000000000000000 : ℝ)+2*(46489885901/29150000000000 : ℝ)*(1219/12500 : ℝ)=(10000280583831181/10000000000000000 : ℝ) by norm_num, show 1+2*(1468061579246551/25000000000000000000 : ℝ)=(12501468061579246551/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24345939369272343/50000000000000000000 : ℝ)+(1468061579246551/25000000000000000000 : ℝ) ≤ ((21993773973223971/22000000000000000 : ℝ)+(46489885901/29150000000000 : ℝ)*((3233/20000 : ℝ)+(1219/12500 : ℝ)))^(2143/512 : ℝ) := by
    rw [show (21993773973223971/22000000000000000 : ℝ)+(46489885901/29150000000000 : ℝ)*((3233/20000 : ℝ)+(1219/12500 : ℝ))=(10001303361321003/10000000000000000 : ℝ) by norm_num, show 1+(24345939369272343/50000000000000000000 : ℝ)+(1468061579246551/25000000000000000000 : ℝ)=(10005456412505553089/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24345939369272343/50000000000000000000 : ℝ) ≤ ((21993773973223971/22000000000000000 : ℝ)+2*(46489885901/29150000000000 : ℝ)*(3233/20000 : ℝ))^(2143/512 : ℝ) := by
    rw [show (21993773973223971/22000000000000000 : ℝ)+2*(46489885901/29150000000000 : ℝ)*(3233/20000 : ℝ)=(400093045552433/400000000000000 : ℝ) by norm_num, show 1+2*(24345939369272343/50000000000000000000 : ℝ)=(25024345939369272343/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21993773973223971/22000000000000000 : ℝ)*(X 1 0+X 2 0)+(46489885901/29150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (1219/12500 : ℝ)) (hi := (3233/20000 : ℝ)) (c := (21993773973223971/22000000000000000 : ℝ)) (alpha := (46489885901/29150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21993773973223971/22000000000000000 : ℝ)*(X 0 1+X 2 1)+(46489885901/29150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (1219/12500 : ℝ)) (hi := (3233/20000 : ℝ)) (c := (21993773973223971/22000000000000000 : ℝ)) (alpha := (46489885901/29150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21993773973223971/22000000000000000 : ℝ)*(X 0 2+X 1 2)+(46489885901/29150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (1219/12500 : ℝ)) (hi := (3233/20000 : ℝ)) (c := (21993773973223971/22000000000000000 : ℝ)) (alpha := (46489885901/29150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-411015839/2000000000 : ℝ)*X 0 0+(5429134313/10000000000 : ℝ)*X 0 1+(5229743859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353234033/10000000000 : ℝ)*X 1 0+(-1078511147/5000000000 : ℝ)*X 1 1+(326858999/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353233801/10000000000 : ℝ)*X 2 0+(1307436053/2500000000 : ℝ)*X 2 1+(-1078511151/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4329396423/10000000000 : ℝ)*X 0 0+(4126437923/10000000000 : ℝ)*X 0 1+(4541719753/10000000000 : ℝ)*X 0 2+(4329396423/10000000000 : ℝ)*X 1 0+(4126437923/10000000000 : ℝ)*X 1 1+(4541719753/10000000000 : ℝ)*X 1 2+(4329396423/10000000000 : ℝ)*X 2 0+(4126437923/10000000000 : ℝ)*X 2 1+(4541719753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1027549693/5000000000 : ℝ)*X 0 0+(5230582473/10000000000 : ℝ)*X 0 1+(2714145281/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060392639/2000000000 : ℝ)*X 1 0+(-97923799/500000000 : ℝ)*X 1 1+(135707269/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060392979/2000000000 : ℝ)*X 2 0+(169634049/312500000 : ℝ)*X 2 1+(-979237649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4329439109/10000000000 : ℝ)*X 0 0+(4539973123/10000000000 : ℝ)*X 0 1+(258012147/625000000 : ℝ)*X 0 2+(4329439109/10000000000 : ℝ)*X 1 0+(4539973123/10000000000 : ℝ)*X 1 1+(258012147/625000000 : ℝ)*X 1 2+(4329439109/10000000000 : ℝ)*X 2 0+(4539973123/10000000000 : ℝ)*X 2 1+(258012147/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6878546073094286816451867/1821875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (719160059/100000000000000 : ℝ)*(base19) + (358465863/100000000000000 : ℝ)*(base23) + (8405451/5000000000000 : ℝ)*(upper3) + (38366387/50000000000000 : ℝ)*(upper4) + (8237631/50000000000000 : ℝ)*(upper5) + (14498691854991/390625000000 : ℝ)*(major0) + (14498691854991/390625000000 : ℝ)*(major1) + (14498691854991/390625000000 : ℝ)*(major2) + (5015301813744991/100000000000000 : ℝ)*(sp0) + (200612522542619/4000000000000 : ℝ)*(sp1) + (5015313424259671/100000000000000 : ℝ)*(sp2) + (1204004459096041/50000000000000 : ℝ)*(sp3) + (187015321/1562500000000 : ℝ)*(sp4) + (1850746681/25000000000000 : ℝ)*(sp7) + (481603264235761/20000000000000 : ℝ)*(f.failure) + (2507656891362767/50000000000000 : ℝ)*(f.sum) + (21797338304103/2915000000000000000000000000 : ℝ)*base66 + (932430824063543/1821875000000000000000000000000 : ℝ)*base68 + (14121236020044793/1821875000000000000000000000000 : ℝ)*base70 + (4961682366726043/1821875000000000000000000000000 : ℝ)*base72 + (432849059479/91093750000000000000000000 : ℝ)*base74 + (1829889313494791/910937500000000000000000000000 : ℝ)*base75 + (11244754233061457/1821875000000000000000000000000 : ℝ)*base77 + (5934475532861459/910937500000000000000000000000 : ℝ)*base80 + (1536867916993/182187500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (822463/125000000000000000000 : ℝ)*base90 + (822463/125000000000000000000 : ℝ)*base92 + (822463/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105986935825924132814675397/14575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1764876337/100000000000000 : ℝ)*(base19) + (3878632937/100000000000000 : ℝ)*(base23) + (22670479/6250000000000 : ℝ)*(upper3) + (50036419/50000000000000 : ℝ)*(lower4) + (204423361/100000000000000 : ℝ)*(upper5) + (1871615742386073/50000000000000 : ℝ)*(major0) + (1871615742386073/50000000000000 : ℝ)*(major1) + (1871615742386073/50000000000000 : ℝ)*(major2) + (85664673/312500000000 : ℝ)*(sp1) + (229584949/390625000000 : ℝ)*(sp2) + (2528983548874317/50000000000000 : ℝ)*(sp4) + (2528968960088469/50000000000000 : ℝ)*(sp5) + (2528952222684377/50000000000000 : ℝ)*(sp6) + (607123907350321/25000000000000 : ℝ)*(sp7) + (607123907350321/25000000000000 : ℝ)*(f.failure) + (2528983548874317/50000000000000 : ℝ)*(f.sum) + (2271612076047/728750000000000000000000000 : ℝ)*base66 + (191409274537018201/58300000000000000000000000000000 : ℝ)*base68 + (166770857128381799/58300000000000000000000000000000 : ℝ)*base69 + (71055799972618201/58300000000000000000000000000000 : ℝ)*base72 + (363224502061/364375000000000000000000000 : ℝ)*base74 + (1168568186411218201/58300000000000000000000000000000 : ℝ)*base76 + (100331796999818201/58300000000000000000000000000000 : ℝ)*base78 + (682759022936418201/58300000000000000000000000000000 : ℝ)*base80 + (279820784673/45546875000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (783943/156250000000000000000 : ℝ)*base90 + (783943/156250000000000000000 : ℝ)*base92 + (783943/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1327_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3233/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1219/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5403/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (601/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1327_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1327_s4_0 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1028332191/5000000000 : ℝ)*x 0 + (5416329029/10000000000 : ℝ)*x 1 + (5118661/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1028332191/5000000000 : ℝ)^4287 ≤ (12520430143643/100000000000000 : ℝ)^3263 := by
    have hnat : (1028332191 : ℕ)^4287*100000000000000^3263 ≤ 12520430143643^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028332191 5000000000 12520430143643 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416329029/10000000000 : ℝ)^4287 ≤ (11170585241981/25000000000000 : ℝ)^3263 := by
    have hnat : (5416329029 : ℕ)^4287*25000000000000^3263 ≤ 11170585241981^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416329029 10000000000 11170585241981 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5118661/9765625 : ℝ)^4287 ≤ (1711889154703/4000000000000 : ℝ)^3263 := by
    have hnat : (5118661 : ℕ)^4287*4000000000000^3263 ≤ 1711889154703^3263*9765625^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5118661 9765625 1711889154703 4000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1028332191/5000000000 : ℝ), (5416329029/10000000000 : ℝ), (5118661/9765625 : ℝ)] ![(12520430143643/100000000000000 : ℝ), (11170585241981/25000000000000 : ℝ), (1711889154703/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1028332191/5000000000 : ℝ)|^4287 ≤ (12520430143643/100000000000000 : ℝ)^3263
        have hw : |(-1028332191/5000000000 : ℝ)|=(1028332191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416329029/10000000000 : ℝ)|^4287 ≤ (11170585241981/25000000000000 : ℝ)^3263
        have hw : |(5416329029/10000000000 : ℝ)|=(5416329029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5118661/9765625 : ℝ)|^4287 ≤ (1711889154703/4000000000000 : ℝ)^3263
        have hw : |(5118661/9765625 : ℝ)|=(5118661/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s4_1 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349978659/10000000000 : ℝ)*x 0 + (-429160617/2000000000 : ℝ)*x 1 + (262075437/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349978659/10000000000 : ℝ)^4287 ≤ (43964591808517/100000000000000 : ℝ)^3263 := by
    have hnat : (5349978659 : ℕ)^4287*100000000000000^3263 ≤ 43964591808517^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349978659 10000000000 43964591808517 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429160617/2000000000 : ℝ)^4287 ≤ (2647636128591/20000000000000 : ℝ)^3263 := by
    have hnat : (429160617 : ℕ)^4287*20000000000000^3263 ≤ 2647636128591^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429160617 2000000000 2647636128591 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262075437/500000000 : ℝ)^4287 ≤ (42797227537373/100000000000000 : ℝ)^3263 := by
    have hnat : (262075437 : ℕ)^4287*100000000000000^3263 ≤ 42797227537373^3263*500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262075437 500000000 42797227537373 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349978659/10000000000 : ℝ), (-429160617/2000000000 : ℝ), (262075437/500000000 : ℝ)] ![(43964591808517/100000000000000 : ℝ), (2647636128591/20000000000000 : ℝ), (42797227537373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349978659/10000000000 : ℝ)|^4287 ≤ (43964591808517/100000000000000 : ℝ)^3263
        have hw : |(5349978659/10000000000 : ℝ)|=(5349978659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429160617/2000000000 : ℝ)|^4287 ≤ (2647636128591/20000000000000 : ℝ)^3263
        have hw : |(-429160617/2000000000 : ℝ)|=(429160617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262075437/500000000 : ℝ)|^4287 ≤ (42797227537373/100000000000000 : ℝ)^3263
        have hw : |(262075437/500000000 : ℝ)|=(262075437/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s4_2 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337494679/2500000000 : ℝ)*x 0 + (5241508471/10000000000 : ℝ)*x 1 + (-429160673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337494679/2500000000 : ℝ)^4287 ≤ (10991148105981/25000000000000 : ℝ)^3263 := by
    have hnat : (1337494679 : ℕ)^4287*25000000000000^3263 ≤ 10991148105981^3263*2500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337494679 2500000000 10991148105981 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241508471/10000000000 : ℝ)^4287 ≤ (21398612325847/50000000000000 : ℝ)^3263 := by
    have hnat : (5241508471 : ℕ)^4287*50000000000000^3263 ≤ 21398612325847^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241508471 10000000000 21398612325847 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429160673/2000000000 : ℝ)^4287 ≤ (1323818291247/10000000000000 : ℝ)^3263 := by
    have hnat : (429160673 : ℕ)^4287*10000000000000^3263 ≤ 1323818291247^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429160673 2000000000 1323818291247 10000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337494679/2500000000 : ℝ), (5241508471/10000000000 : ℝ), (-429160673/2000000000 : ℝ)] ![(10991148105981/25000000000000 : ℝ), (21398612325847/50000000000000 : ℝ), (1323818291247/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337494679/2500000000 : ℝ)|^4287 ≤ (10991148105981/25000000000000 : ℝ)^3263
        have hw : |(1337494679/2500000000 : ℝ)|=(1337494679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241508471/10000000000 : ℝ)|^4287 ≤ (21398612325847/50000000000000 : ℝ)^3263
        have hw : |(5241508471/10000000000 : ℝ)|=(5241508471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429160673/2000000000 : ℝ)|^4287 ≤ (1323818291247/10000000000000 : ℝ)^3263
        have hw : |(-429160673/2000000000 : ℝ)|=(429160673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s4_3 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165179337/5000000000 : ℝ)*x 0 + (4151904599/10000000000 : ℝ)*x 1 + (4516013331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165179337/5000000000 : ℝ)^4287 ≤ (4162624235023/12500000000000 : ℝ)^3263 := by
    have hnat : (2165179337 : ℕ)^4287*12500000000000^3263 ≤ 4162624235023^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165179337 5000000000 4162624235023 12500000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4151904599/10000000000 : ℝ)^4287 ≤ (15754881240741/50000000000000 : ℝ)^3263 := by
    have hnat : (4151904599 : ℕ)^4287*50000000000000^3263 ≤ 15754881240741^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151904599 10000000000 15754881240741 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4516013331/10000000000 : ℝ)^4287 ≤ (2199327726167/6250000000000 : ℝ)^3263 := by
    have hnat : (4516013331 : ℕ)^4287*6250000000000^3263 ≤ 2199327726167^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516013331 10000000000 2199327726167 6250000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165179337/5000000000 : ℝ), (4151904599/10000000000 : ℝ), (4516013331/10000000000 : ℝ)] ![(4162624235023/12500000000000 : ℝ), (15754881240741/50000000000000 : ℝ), (2199327726167/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165179337/5000000000 : ℝ)|^4287 ≤ (4162624235023/12500000000000 : ℝ)^3263
        have hw : |(2165179337/5000000000 : ℝ)|=(2165179337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4151904599/10000000000 : ℝ)|^4287 ≤ (15754881240741/50000000000000 : ℝ)^3263
        have hw : |(4151904599/10000000000 : ℝ)|=(4151904599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4516013331/10000000000 : ℝ)|^4287 ≤ (2199327726167/6250000000000 : ℝ)^3263
        have hw : |(4516013331/10000000000 : ℝ)|=(4516013331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s4_4 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1028339019/5000000000 : ℝ)*x 0 + (655269239/1250000000 : ℝ)*x 1 + (5415680487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1028339019/5000000000 : ℝ)^4287 ≤ (12520539367169/100000000000000 : ℝ)^3263 := by
    have hnat : (1028339019 : ℕ)^4287*100000000000000^3263 ≤ 12520539367169^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028339019 5000000000 12520539367169 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655269239/1250000000 : ℝ)^4287 ≤ (42804148709177/100000000000000 : ℝ)^3263 := by
    have hnat : (655269239 : ℕ)^4287*100000000000000^3263 ≤ 42804148709177^3263*1250000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655269239 1250000000 42804148709177 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415680487/10000000000 : ℝ)^4287 ≤ (44675311908161/100000000000000 : ℝ)^3263 := by
    have hnat : (5415680487 : ℕ)^4287*100000000000000^3263 ≤ 44675311908161^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415680487 10000000000 44675311908161 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1028339019/5000000000 : ℝ), (655269239/1250000000 : ℝ), (5415680487/10000000000 : ℝ)] ![(12520539367169/100000000000000 : ℝ), (42804148709177/100000000000000 : ℝ), (44675311908161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1028339019/5000000000 : ℝ)|^4287 ≤ (12520539367169/100000000000000 : ℝ)^3263
        have hw : |(-1028339019/5000000000 : ℝ)|=(1028339019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655269239/1250000000 : ℝ)|^4287 ≤ (42804148709177/100000000000000 : ℝ)^3263
        have hw : |(655269239/1250000000 : ℝ)|=(655269239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415680487/10000000000 : ℝ)|^4287 ≤ (44675311908161/100000000000000 : ℝ)^3263
        have hw : |(5415680487/10000000000 : ℝ)|=(5415680487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s4_5 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305027523/10000000000 : ℝ)*x 0 + (-1971631529/10000000000 : ℝ)*x 1 + (1083136097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305027523/10000000000 : ℝ)^4287 ≤ (8695982600983/20000000000000 : ℝ)^3263 := by
    have hnat : (5305027523 : ℕ)^4287*20000000000000^3263 ≤ 8695982600983^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305027523 10000000000 8695982600983 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1971631529/10000000000 : ℝ)^4287 ≤ (236895501807/2000000000000 : ℝ)^3263 := by
    have hnat : (1971631529 : ℕ)^4287*2000000000000^3263 ≤ 236895501807^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971631529 10000000000 236895501807 2000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083136097/2000000000 : ℝ)^4287 ≤ (8935062377297/20000000000000 : ℝ)^3263 := by
    have hnat : (1083136097 : ℕ)^4287*20000000000000^3263 ≤ 8935062377297^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083136097 2000000000 8935062377297 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305027523/10000000000 : ℝ), (-1971631529/10000000000 : ℝ), (1083136097/2000000000 : ℝ)] ![(8695982600983/20000000000000 : ℝ), (236895501807/2000000000000 : ℝ), (8935062377297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305027523/10000000000 : ℝ)|^4287 ≤ (8695982600983/20000000000000 : ℝ)^3263
        have hw : |(5305027523/10000000000 : ℝ)|=(5305027523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1971631529/10000000000 : ℝ)|^4287 ≤ (236895501807/2000000000000 : ℝ)^3263
        have hw : |(-1971631529/10000000000 : ℝ)|=(1971631529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083136097/2000000000 : ℝ)|^4287 ≤ (8935062377297/20000000000000 : ℝ)^3263
        have hw : |(1083136097/2000000000 : ℝ)|=(1083136097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s4_6 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652513769/5000000000 : ℝ)*x 0 + (1083136093/2000000000 : ℝ)*x 1 + (-394326307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652513769/5000000000 : ℝ)^4287 ≤ (10869978291609/25000000000000 : ℝ)^3263 := by
    have hnat : (2652513769 : ℕ)^4287*25000000000000^3263 ≤ 10869978291609^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652513769 5000000000 10869978291609 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083136093/2000000000 : ℝ)^4287 ≤ (11168827917431/25000000000000 : ℝ)^3263 := by
    have hnat : (1083136093 : ℕ)^4287*25000000000000^3263 ≤ 11168827917431^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083136093 2000000000 11168827917431 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394326307/2000000000 : ℝ)^4287 ≤ (2961193784427/25000000000000 : ℝ)^3263 := by
    have hnat : (394326307 : ℕ)^4287*25000000000000^3263 ≤ 2961193784427^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394326307 2000000000 2961193784427 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652513769/5000000000 : ℝ), (1083136093/2000000000 : ℝ), (-394326307/2000000000 : ℝ)] ![(10869978291609/25000000000000 : ℝ), (11168827917431/25000000000000 : ℝ), (2961193784427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652513769/5000000000 : ℝ)|^4287 ≤ (10869978291609/25000000000000 : ℝ)^3263
        have hw : |(2652513769/5000000000 : ℝ)|=(2652513769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083136093/2000000000 : ℝ)|^4287 ≤ (11168827917431/25000000000000 : ℝ)^3263
        have hw : |(1083136093/2000000000 : ℝ)|=(1083136093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394326307/2000000000 : ℝ)|^4287 ≤ (2961193784427/25000000000000 : ℝ)^3263
        have hw : |(-394326307/2000000000 : ℝ)|=(394326307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s4_7 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4330386927/10000000000 : ℝ)*x 0 + (4514669411/10000000000 : ℝ)*x 1 + (4153255683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330386927/10000000000 : ℝ)^4287 ≤ (1332051173331/4000000000000 : ℝ)^3263 := by
    have hnat : (4330386927 : ℕ)^4287*4000000000000^3263 ≤ 1332051173331^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330386927 10000000000 1332051173331 4000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514669411/10000000000 : ℝ)^4287 ≤ (2198467873031/6250000000000 : ℝ)^3263 := by
    have hnat : (4514669411 : ℕ)^4287*6250000000000^3263 ≤ 2198467873031^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514669411 10000000000 2198467873031 6250000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4153255683/10000000000 : ℝ)^4287 ≤ (31523234686943/100000000000000 : ℝ)^3263 := by
    have hnat : (4153255683 : ℕ)^4287*100000000000000^3263 ≤ 31523234686943^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153255683 10000000000 31523234686943 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330386927/10000000000 : ℝ), (4514669411/10000000000 : ℝ), (4153255683/10000000000 : ℝ)] ![(1332051173331/4000000000000 : ℝ), (2198467873031/6250000000000 : ℝ), (31523234686943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330386927/10000000000 : ℝ)|^4287 ≤ (1332051173331/4000000000000 : ℝ)^3263
        have hw : |(4330386927/10000000000 : ℝ)|=(4330386927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514669411/10000000000 : ℝ)|^4287 ≤ (2198467873031/6250000000000 : ℝ)^3263
        have hw : |(4514669411/10000000000 : ℝ)|=(4514669411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4153255683/10000000000 : ℝ)|^4287 ≤ (31523234686943/100000000000000 : ℝ)^3263
        have hw : |(4153255683/10000000000 : ℝ)|=(4153255683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1327_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (601/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5403/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11057/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14757/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (601/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5403/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (601/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5403/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (601/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5403/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (601/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5403/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (601/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5403/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (601/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5403/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5403/50000 : ℝ) ^ (2143/512 : ℝ) ≤ (9023175543450447/100000000000000000000 : ℝ) := by
    have hpowers : (5403/50000 : ℝ)^2143 ≤ (9023175543450447/100000000000000000000 : ℝ)^512 := by
      have hnat : (5403 : ℕ)^2143*100000000000000000000^512 ≤ 9023175543450447^512*50000^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5403 50000 9023175543450447 100000000000000000000 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5403/50000 : ℝ)) (X := (9023175543450447/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hpowhi : (601/4000 : ℝ) ^ (2143/512 : ℝ) ≤ (35852415594700763/100000000000000000000 : ℝ) := by
    have hpowers : (601/4000 : ℝ)^2143 ≤ (35852415594700763/100000000000000000000 : ℝ)^512 := by
      have hnat : (601 : ℕ)^2143*100000000000000000000^512 ≤ 35852415594700763^512*4000^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        601 4000 35852415594700763 100000000000000000000 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (601/4000 : ℝ)) (X := (35852415594700763/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009023175543450447/50000000000000000000 : ℝ) ≤ (5000215564565937/5000000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (50009023175543450447/50000000000000000000 : ℝ)^512 ≤ (5000215564565937/5000000000000000 : ℝ)^2143 := by
      have hnat : (50009023175543450447 : ℕ)^512*5000000000000000^2143 ≤ 5000215564565937^2143*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009023175543450447 50000000000000000000 5000215564565937 5000000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000215564565937/5000000000000000 : ℝ)) (X := (50009023175543450447/50000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004487559113815121/10000000000000000000 : ℝ) ≤ (5000535986468251/5000000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (10004487559113815121/10000000000000000000 : ℝ)^512 ≤ (5000535986468251/5000000000000000 : ℝ)^2143 := by
      have hnat : (10004487559113815121 : ℕ)^512*5000000000000000^2143 ≤ 5000535986468251^2143*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004487559113815121 10000000000000000000 5000535986468251 5000000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000535986468251/5000000000000000 : ℝ)) (X := (10004487559113815121/10000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035852415594700763/50000000000000000000 : ℝ) ≤ (1000171281674113/1000000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (50035852415594700763/50000000000000000000 : ℝ)^512 ≤ (1000171281674113/1000000000000000 : ℝ)^2143 := by
      have hnat : (50035852415594700763 : ℕ)^512*1000000000000000^2143 ≤ 1000171281674113^2143*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035852415594700763 50000000000000000000 1000171281674113 1000000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000171281674113/1000000000000000 : ℝ)) (X := (50035852415594700763/50000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9023175543450447/100000000000000000000 : ℝ) ≤ ((4217796901750175607/4219000000000000000 : ℝ)+2*(160210951157/105475000000000 : ℝ)*(5403/50000 : ℝ))^(2143/512 : ℝ) := by
    rw [show (4217796901750175607/4219000000000000000 : ℝ)+2*(160210951157/105475000000000 : ℝ)*(5403/50000 : ℝ)=(5000215564565937/5000000000000000 : ℝ) by norm_num, show 1+2*(9023175543450447/100000000000000000000 : ℝ)=(50009023175543450447/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35852415594700763/100000000000000000000 : ℝ)+(9023175543450447/100000000000000000000 : ℝ) ≤ ((4217796901750175607/4219000000000000000 : ℝ)+(160210951157/105475000000000 : ℝ)*((601/4000 : ℝ)+(5403/50000 : ℝ)))^(2143/512 : ℝ) := by
    rw [show (4217796901750175607/4219000000000000000 : ℝ)+(160210951157/105475000000000 : ℝ)*((601/4000 : ℝ)+(5403/50000 : ℝ))=(5000535986468251/5000000000000000 : ℝ) by norm_num, show 1+(35852415594700763/100000000000000000000 : ℝ)+(9023175543450447/100000000000000000000 : ℝ)=(10004487559113815121/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35852415594700763/100000000000000000000 : ℝ) ≤ ((4217796901750175607/4219000000000000000 : ℝ)+2*(160210951157/105475000000000 : ℝ)*(601/4000 : ℝ))^(2143/512 : ℝ) := by
    rw [show (4217796901750175607/4219000000000000000 : ℝ)+2*(160210951157/105475000000000 : ℝ)*(601/4000 : ℝ)=(1000171281674113/1000000000000000 : ℝ) by norm_num, show 1+2*(35852415594700763/100000000000000000000 : ℝ)=(50035852415594700763/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4217796901750175607/4219000000000000000 : ℝ)*(X 1 0+X 2 0)+(160210951157/105475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (5403/50000 : ℝ)) (hi := (601/4000 : ℝ)) (c := (4217796901750175607/4219000000000000000 : ℝ)) (alpha := (160210951157/105475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4217796901750175607/4219000000000000000 : ℝ)*(X 0 1+X 2 1)+(160210951157/105475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (5403/50000 : ℝ)) (hi := (601/4000 : ℝ)) (c := (4217796901750175607/4219000000000000000 : ℝ)) (alpha := (160210951157/105475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4217796901750175607/4219000000000000000 : ℝ)*(X 0 2+X 1 2)+(160210951157/105475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (5403/50000 : ℝ)) (hi := (601/4000 : ℝ)) (c := (4217796901750175607/4219000000000000000 : ℝ)) (alpha := (160210951157/105475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1028332191/5000000000 : ℝ)*X 0 0+(5416329029/10000000000 : ℝ)*X 0 1+(5118661/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349978659/10000000000 : ℝ)*X 1 0+(-429160617/2000000000 : ℝ)*X 1 1+(262075437/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337494679/2500000000 : ℝ)*X 2 0+(5241508471/10000000000 : ℝ)*X 2 1+(-429160673/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2165179337/5000000000 : ℝ)*X 0 0+(4151904599/10000000000 : ℝ)*X 0 1+(4516013331/10000000000 : ℝ)*X 0 2+(2165179337/5000000000 : ℝ)*X 1 0+(4151904599/10000000000 : ℝ)*X 1 1+(4516013331/10000000000 : ℝ)*X 1 2+(2165179337/5000000000 : ℝ)*X 2 0+(4151904599/10000000000 : ℝ)*X 2 1+(4516013331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1028339019/5000000000 : ℝ)*X 0 0+(655269239/1250000000 : ℝ)*X 0 1+(5415680487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305027523/10000000000 : ℝ)*X 1 0+(-1971631529/10000000000 : ℝ)*X 1 1+(1083136097/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652513769/5000000000 : ℝ)*X 2 0+(1083136093/2000000000 : ℝ)*X 2 1+(-394326307/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4330386927/10000000000 : ℝ)*X 0 0+(4514669411/10000000000 : ℝ)*X 0 1+(4153255683/10000000000 : ℝ)*X 0 2+(4330386927/10000000000 : ℝ)*X 1 0+(4514669411/10000000000 : ℝ)*X 1 1+(4153255683/10000000000 : ℝ)*X 1 2+(4330386927/10000000000 : ℝ)*X 2 0+(4514669411/10000000000 : ℝ)*X 2 1+(4153255683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (555725737027282271271419157/105475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (579230951/50000000000000 : ℝ)*(base19) + (685429217/50000000000000 : ℝ)*(base23) + (90145403/50000000000000 : ℝ)*(upper3) + (84029673/100000000000000 : ℝ)*(lower4) + (2116666159444217/50000000000000 : ℝ)*(major0) + (2116666159444217/50000000000000 : ℝ)*(major1) + (2116666159444217/50000000000000 : ℝ)*(major2) + (5720188974929383/100000000000000 : ℝ)*(sp0) + (1430051260669743/25000000000000 : ℝ)*(sp1) + (2860102081095361/50000000000000 : ℝ)*(sp2) + (686611047690131/25000000000000 : ℝ)*(sp3) + (1722621149/10000000000000 : ℝ)*(sp4) + (334045859/50000000000000 : ℝ)*(sp6) + (1758781137/12500000000000 : ℝ)*(sp7) + (137322913050481/5000000000000 : ℝ)*(f.failure) + (2860103100570437/50000000000000 : ℝ)*(f.sum) + (7321136716219/10547500000000000000000000000 : ℝ)*base66 + (43679771340324719/210950000000000000000000000000000 : ℝ)*base67 + (1217810560032925281/210950000000000000000000000000000 : ℝ)*base70 + (1588978595856825281/210950000000000000000000000000000 : ℝ)*base72 + (1655497208489/2636875000000000000000000000 : ℝ)*base73 + (934181690314025281/210950000000000000000000000000000 : ℝ)*base76 + (2177671892209574719/210950000000000000000000000000000 : ℝ)*base77 + (2418251639707425281/210950000000000000000000000000000 : ℝ)*base80 + (504565306283/329609375000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5223/31250000000000000000 : ℝ)*base90 + (5223/31250000000000000000 : ℝ)*base92 + (5223/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50968319346222177461306037/10547500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5411413/625000000000 : ℝ)*(base19) + (188567387/20000000000000 : ℝ)*(base23) + (98218263/100000000000000 : ℝ)*(upper3) + (29045561/100000000000000 : ℝ)*(lower4) + (107445879/100000000000000 : ℝ)*(upper5) + (213242947082999/5000000000000 : ℝ)*(major0) + (213242947082999/5000000000000 : ℝ)*(major1) + (213242947082999/5000000000000 : ℝ)*(major2) + (8541899671/50000000000000 : ℝ)*(sp1) + (17787814281/100000000000000 : ℝ)*(sp2) + (1440701484936561/25000000000000 : ℝ)*(sp4) + (5762787990120823/100000000000000 : ℝ)*(sp5) + (1440696802273757/25000000000000 : ℝ)*(sp6) + (172931986406137/6250000000000 : ℝ)*(sp7) + (172931986406137/6250000000000 : ℝ)*(f.failure) + (1440701484936561/25000000000000 : ℝ)*(f.sum) + (688137092511/105475000000000000000000000 : ℝ)*base66 + (108414183478874607/21095000000000000000000000000000 : ℝ)*base68 + (225344918662654607/21095000000000000000000000000000 : ℝ)*base70 + (293775491793219607/21095000000000000000000000000000 : ℝ)*base72 + (23915115640537/4219000000000000000000000000 : ℝ)*base74 + (563922778213319607/21095000000000000000000000000000 : ℝ)*base76 + (138960772999254607/21095000000000000000000000000000 : ℝ)*base78 + (79568792786959607/21095000000000000000000000000000 : ℝ)*base80 + (2135289225059/4219000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (620029/39062500000000000000 : ℝ)*base89 + (620029/39062500000000000000 : ℝ)*base91 + (620029/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1327_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (601/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5403/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11057/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1327_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1327_s5_0 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411389457/2000000000 : ℝ)*x 0 + (270696107/500000000 : ℝ)*x 1 + (5243729413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411389457/2000000000 : ℝ)^4287 ≤ (12522692907111/100000000000000 : ℝ)^3263 := by
    have hnat : (411389457 : ℕ)^4287*100000000000000^3263 ≤ 12522692907111^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411389457 2000000000 12522692907111 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270696107/500000000 : ℝ)^4287 ≤ (2791015989647/6250000000000 : ℝ)^3263 := by
    have hnat : (270696107 : ℕ)^4287*6250000000000^3263 ≤ 2791015989647^3263*500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270696107 500000000 2791015989647 6250000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243729413/10000000000 : ℝ)^4287 ≤ (8564210247467/20000000000000 : ℝ)^3263 := by
    have hnat : (5243729413 : ℕ)^4287*20000000000000^3263 ≤ 8564210247467^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243729413 10000000000 8564210247467 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411389457/2000000000 : ℝ), (270696107/500000000 : ℝ), (5243729413/10000000000 : ℝ)] ![(12522692907111/100000000000000 : ℝ), (2791015989647/6250000000000 : ℝ), (8564210247467/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411389457/2000000000 : ℝ)|^4287 ≤ (12522692907111/100000000000000 : ℝ)^3263
        have hw : |(-411389457/2000000000 : ℝ)|=(411389457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270696107/500000000 : ℝ)|^4287 ≤ (2791015989647/6250000000000 : ℝ)^3263
        have hw : |(270696107/500000000 : ℝ)|=(270696107/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243729413/10000000000 : ℝ)|^4287 ≤ (8564210247467/20000000000000 : ℝ)^3263
        have hw : |(5243729413/10000000000 : ℝ)|=(5243729413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s5_1 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349364377/10000000000 : ℝ)*x 0 + (-1071840729/5000000000 : ℝ)*x 1 + (524372963/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349364377/10000000000 : ℝ)^4287 ≤ (21978979882477/50000000000000 : ℝ)^3263 := by
    have hnat : (5349364377 : ℕ)^4287*50000000000000^3263 ≤ 21978979882477^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349364377 10000000000 21978979882477 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071840729/5000000000 : ℝ)^4287 ≤ (13220986660359/100000000000000 : ℝ)^3263 := by
    have hnat : (1071840729 : ℕ)^4287*100000000000000^3263 ≤ 13220986660359^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071840729 5000000000 13220986660359 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524372963/1000000000 : ℝ)^4287 ≤ (42821053565497/100000000000000 : ℝ)^3263 := by
    have hnat : (524372963 : ℕ)^4287*100000000000000^3263 ≤ 42821053565497^3263*1000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524372963 1000000000 42821053565497 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349364377/10000000000 : ℝ), (-1071840729/5000000000 : ℝ), (524372963/1000000000 : ℝ)] ![(21978979882477/50000000000000 : ℝ), (13220986660359/100000000000000 : ℝ), (42821053565497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349364377/10000000000 : ℝ)|^4287 ≤ (21978979882477/50000000000000 : ℝ)^3263
        have hw : |(5349364377/10000000000 : ℝ)|=(5349364377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1071840729/5000000000 : ℝ)|^4287 ≤ (13220986660359/100000000000000 : ℝ)^3263
        have hw : |(-1071840729/5000000000 : ℝ)|=(1071840729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524372963/1000000000 : ℝ)|^4287 ≤ (42821053565497/100000000000000 : ℝ)^3263
        have hw : |(524372963/1000000000 : ℝ)|=(524372963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s5_2 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349363777/10000000000 : ℝ)*x 0 + (524372991/1000000000 : ℝ)*x 1 + (-1071840943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349363777/10000000000 : ℝ)^4287 ≤ (43957953287221/100000000000000 : ℝ)^3263 := by
    have hnat : (5349363777 : ℕ)^4287*100000000000000^3263 ≤ 43957953287221^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349363777 10000000000 43957953287221 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524372991/1000000000 : ℝ)^4287 ≤ (42821056569577/100000000000000 : ℝ)^3263 := by
    have hnat : (524372991 : ℕ)^4287*100000000000000^3263 ≤ 42821056569577^3263*1000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524372991 1000000000 42821056569577 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071840943/5000000000 : ℝ)^4287 ≤ (13220990128397/100000000000000 : ℝ)^3263 := by
    have hnat : (1071840943 : ℕ)^4287*100000000000000^3263 ≤ 13220990128397^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071840943 5000000000 13220990128397 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349363777/10000000000 : ℝ), (524372991/1000000000 : ℝ), (-1071840943/5000000000 : ℝ)] ![(43957953287221/100000000000000 : ℝ), (42821056569577/100000000000000 : ℝ), (13220990128397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349363777/10000000000 : ℝ)|^4287 ≤ (43957953287221/100000000000000 : ℝ)^3263
        have hw : |(5349363777/10000000000 : ℝ)|=(5349363777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524372991/1000000000 : ℝ)|^4287 ≤ (42821056569577/100000000000000 : ℝ)^3263
        have hw : |(524372991/1000000000 : ℝ)|=(524372991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1071840943/5000000000 : ℝ)|^4287 ≤ (13220990128397/100000000000000 : ℝ)^3263
        have hw : |(-1071840943/5000000000 : ℝ)|=(1071840943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s5_3 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165262687/5000000000 : ℝ)*x 0 + (207835179/500000000 : ℝ)*x 1 + (2255586557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165262687/5000000000 : ℝ)^4287 ≤ (4162834766953/12500000000000 : ℝ)^3263 := by
    have hnat : (2165262687 : ℕ)^4287*12500000000000^3263 ≤ 4162834766953^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165262687 5000000000 4162834766953 12500000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207835179/500000000 : ℝ)^4287 ≤ (6311524259313/20000000000000 : ℝ)^3263 := by
    have hnat : (207835179 : ℕ)^4287*20000000000000^3263 ≤ 6311524259313^3263*500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207835179 500000000 6311524259313 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255586557/5000000000 : ℝ)^4287 ≤ (35139700550653/100000000000000 : ℝ)^3263 := by
    have hnat : (2255586557 : ℕ)^4287*100000000000000^3263 ≤ 35139700550653^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255586557 5000000000 35139700550653 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165262687/5000000000 : ℝ), (207835179/500000000 : ℝ), (2255586557/5000000000 : ℝ)] ![(4162834766953/12500000000000 : ℝ), (6311524259313/20000000000000 : ℝ), (35139700550653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165262687/5000000000 : ℝ)|^4287 ≤ (4162834766953/12500000000000 : ℝ)^3263
        have hw : |(2165262687/5000000000 : ℝ)|=(2165262687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207835179/500000000 : ℝ)|^4287 ≤ (6311524259313/20000000000000 : ℝ)^3263
        have hw : |(207835179/500000000 : ℝ)|=(207835179/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255586557/5000000000 : ℝ)|^4287 ≤ (35139700550653/100000000000000 : ℝ)^3263
        have hw : |(2255586557/5000000000 : ℝ)|=(2255586557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s5_4 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-64279987/312500000 : ℝ)*x 0 + (5244341163/10000000000 : ℝ)*x 1 + (5286433/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64279987/312500000 : ℝ)^4287 ≤ (2504558256261/20000000000000 : ℝ)^3263 := by
    have hnat : (64279987 : ℕ)^4287*20000000000000^3263 ≤ 2504558256261^3263*312500000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64279987 312500000 2504558256261 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244341163/10000000000 : ℝ)^4287 ≤ (21413807367909/50000000000000 : ℝ)^3263 := by
    have hnat : (5244341163 : ℕ)^4287*50000000000000^3263 ≤ 21413807367909^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244341163 10000000000 21413807367909 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5286433/9765625 : ℝ)^4287 ≤ (44649593965211/100000000000000 : ℝ)^3263 := by
    have hnat : (5286433 : ℕ)^4287*100000000000000^3263 ≤ 44649593965211^3263*9765625^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286433 9765625 44649593965211 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-64279987/312500000 : ℝ), (5244341163/10000000000 : ℝ), (5286433/9765625 : ℝ)] ![(2504558256261/20000000000000 : ℝ), (21413807367909/50000000000000 : ℝ), (44649593965211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-64279987/312500000 : ℝ)|^4287 ≤ (2504558256261/20000000000000 : ℝ)^3263
        have hw : |(-64279987/312500000 : ℝ)|=(64279987/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244341163/10000000000 : ℝ)|^4287 ≤ (21413807367909/50000000000000 : ℝ)^3263
        have hw : |(5244341163/10000000000 : ℝ)|=(5244341163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5286433/9765625 : ℝ)|^4287 ≤ (44649593965211/100000000000000 : ℝ)^3263
        have hw : |(5286433/9765625 : ℝ)|=(5286433/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s5_5 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061120661/2000000000 : ℝ)*x 0 + (-1974103639/10000000000 : ℝ)*x 1 + (1082661511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061120661/2000000000 : ℝ)^4287 ≤ (2717882072823/6250000000000 : ℝ)^3263 := by
    have hnat : (1061120661 : ℕ)^4287*6250000000000^3263 ≤ 2717882072823^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061120661 2000000000 2717882072823 6250000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1974103639/10000000000 : ℝ)^4287 ≤ (5932145542177/50000000000000 : ℝ)^3263 := by
    have hnat : (1974103639 : ℕ)^4287*50000000000000^3263 ≤ 5932145542177^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974103639 10000000000 5932145542177 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082661511/2000000000 : ℝ)^4287 ≤ (44649595731569/100000000000000 : ℝ)^3263 := by
    have hnat : (1082661511 : ℕ)^4287*100000000000000^3263 ≤ 44649595731569^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082661511 2000000000 44649595731569 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061120661/2000000000 : ℝ), (-1974103639/10000000000 : ℝ), (1082661511/2000000000 : ℝ)] ![(2717882072823/6250000000000 : ℝ), (5932145542177/50000000000000 : ℝ), (44649595731569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061120661/2000000000 : ℝ)|^4287 ≤ (2717882072823/6250000000000 : ℝ)^3263
        have hw : |(1061120661/2000000000 : ℝ)|=(1061120661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1974103639/10000000000 : ℝ)|^4287 ≤ (5932145542177/50000000000000 : ℝ)^3263
        have hw : |(-1974103639/10000000000 : ℝ)|=(1974103639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082661511/2000000000 : ℝ)|^4287 ≤ (44649595731569/100000000000000 : ℝ)^3263
        have hw : |(1082661511/2000000000 : ℝ)|=(1082661511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s5_6 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061120689/2000000000 : ℝ)*x 0 + (2706653687/5000000000 : ℝ)*x 1 + (-987051849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061120689/2000000000 : ℝ)^4287 ≤ (43486114672747/100000000000000 : ℝ)^3263 := by
    have hnat : (1061120689 : ℕ)^4287*100000000000000^3263 ≤ 43486114672747^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061120689 2000000000 43486114672747 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706653687/5000000000 : ℝ)^4287 ≤ (44649593770153/100000000000000 : ℝ)^3263 := by
    have hnat : (2706653687 : ℕ)^4287*100000000000000^3263 ≤ 44649593770153^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706653687 5000000000 44649593770153 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987051849/5000000000 : ℝ)^4287 ≤ (11864291550219/100000000000000 : ℝ)^3263 := by
    have hnat : (987051849 : ℕ)^4287*100000000000000^3263 ≤ 11864291550219^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987051849 5000000000 11864291550219 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061120689/2000000000 : ℝ), (2706653687/5000000000 : ℝ), (-987051849/5000000000 : ℝ)] ![(43486114672747/100000000000000 : ℝ), (44649593770153/100000000000000 : ℝ), (11864291550219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061120689/2000000000 : ℝ)|^4287 ≤ (43486114672747/100000000000000 : ℝ)^3263
        have hw : |(1061120689/2000000000 : ℝ)|=(1061120689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706653687/5000000000 : ℝ)|^4287 ≤ (44649593770153/100000000000000 : ℝ)^3263
        have hw : |(2706653687/5000000000 : ℝ)|=(2706653687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-987051849/5000000000 : ℝ)|^4287 ≤ (11864291550219/100000000000000 : ℝ)^3263
        have hw : |(-987051849/5000000000 : ℝ)|=(987051849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s5_7 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165275873/5000000000 : ℝ)*x 0 + (4509899403/10000000000 : ℝ)*x 1 + (519747949/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165275873/5000000000 : ℝ)^4287 ≤ (6660588917461/20000000000000 : ℝ)^3263 := by
    have hnat : (2165275873 : ℕ)^4287*20000000000000^3263 ≤ 6660588917461^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165275873 5000000000 6660588917461 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509899403/10000000000 : ℝ)^4287 ≤ (35126665983017/100000000000000 : ℝ)^3263 := by
    have hnat : (4509899403 : ℕ)^4287*100000000000000^3263 ≤ 35126665983017^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509899403 10000000000 35126665983017 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519747949/1250000000 : ℝ)^4287 ≤ (31570389407231/100000000000000 : ℝ)^3263 := by
    have hnat : (519747949 : ℕ)^4287*100000000000000^3263 ≤ 31570389407231^3263*1250000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519747949 1250000000 31570389407231 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165275873/5000000000 : ℝ), (4509899403/10000000000 : ℝ), (519747949/1250000000 : ℝ)] ![(6660588917461/20000000000000 : ℝ), (35126665983017/100000000000000 : ℝ), (31570389407231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165275873/5000000000 : ℝ)|^4287 ≤ (6660588917461/20000000000000 : ℝ)^3263
        have hw : |(2165275873/5000000000 : ℝ)|=(2165275873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509899403/10000000000 : ℝ)|^4287 ≤ (35126665983017/100000000000000 : ℝ)^3263
        have hw : |(4509899403/10000000000 : ℝ)|=(4509899403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519747949/1250000000 : ℝ)|^4287 ≤ (31570389407231/100000000000000 : ℝ)^3263
        have hw : |(519747949/1250000000 : ℝ)|=(519747949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1327_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (347/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14707/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11057/100000 : ℝ) ^ (2143/512 : ℝ) ≤ (9933427577952413/100000000000000000000 : ℝ) := by
    have hpowers : (11057/100000 : ℝ)^2143 ≤ (9933427577952413/100000000000000000000 : ℝ)^512 := by
      have hnat : (11057 : ℕ)^2143*100000000000000000000^512 ≤ 9933427577952413^512*100000^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11057 100000 9933427577952413 100000000000000000000 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11057/100000 : ℝ)) (X := (9933427577952413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14757/100000 : ℝ) ^ (2143/512 : ℝ) ≤ (16625415332937337/50000000000000000000 : ℝ) := by
    have hpowers : (14757/100000 : ℝ)^2143 ≤ (16625415332937337/50000000000000000000 : ℝ)^512 := by
      have hnat : (14757 : ℕ)^2143*50000000000000000000^512 ≤ 16625415332937337^512*100000^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14757 100000 16625415332937337 50000000000000000000 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14757/100000 : ℝ)) (X := (16625415332937337/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009933427577952413/50000000000000000000 : ℝ) ≤ (10000474617868549/10000000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (50009933427577952413/50000000000000000000 : ℝ)^512 ≤ (10000474617868549/10000000000000000 : ℝ)^2143 := by
      have hnat : (50009933427577952413 : ℕ)^512*10000000000000000^2143 ≤ 10000474617868549^2143*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009933427577952413 50000000000000000000 10000474617868549 10000000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000474617868549/10000000000000000 : ℝ)) (X := (50009933427577952413/50000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043184258243827087/100000000000000000000 : ℝ) ≤ (10001031577585741/10000000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (100043184258243827087/100000000000000000000 : ℝ)^512 ≤ (10001031577585741/10000000000000000 : ℝ)^2143 := by
      have hnat : (100043184258243827087 : ℕ)^512*10000000000000000^2143 ≤ 10001031577585741^2143*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043184258243827087 100000000000000000000 10001031577585741 10000000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001031577585741/10000000000000000 : ℝ)) (X := (100043184258243827087/100000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016625415332937337/25000000000000000000 : ℝ) ≤ (10001588537302933/10000000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (25016625415332937337/25000000000000000000 : ℝ)^512 ≤ (10001588537302933/10000000000000000 : ℝ)^2143 := by
      have hnat : (25016625415332937337 : ℕ)^512*10000000000000000^2143 ≤ 10001588537302933^2143*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016625415332937337 25000000000000000000 10001588537302933 10000000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001588537302933/10000000000000000 : ℝ)) (X := (25016625415332937337/25000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9933427577952413/100000000000000000000 : ℝ) ≤ ((9247359869731911853/9250000000000000000 : ℝ)+2*(69619964649/46250000000000 : ℝ)*(11057/100000 : ℝ))^(2143/512 : ℝ) := by
    rw [show (9247359869731911853/9250000000000000000 : ℝ)+2*(69619964649/46250000000000 : ℝ)*(11057/100000 : ℝ)=(10000474617868549/10000000000000000 : ℝ) by norm_num, show 1+2*(9933427577952413/100000000000000000000 : ℝ)=(50009933427577952413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16625415332937337/50000000000000000000 : ℝ)+(9933427577952413/100000000000000000000 : ℝ) ≤ ((9247359869731911853/9250000000000000000 : ℝ)+(69619964649/46250000000000 : ℝ)*((14757/100000 : ℝ)+(11057/100000 : ℝ)))^(2143/512 : ℝ) := by
    rw [show (9247359869731911853/9250000000000000000 : ℝ)+(69619964649/46250000000000 : ℝ)*((14757/100000 : ℝ)+(11057/100000 : ℝ))=(10001031577585741/10000000000000000 : ℝ) by norm_num, show 1+(16625415332937337/50000000000000000000 : ℝ)+(9933427577952413/100000000000000000000 : ℝ)=(100043184258243827087/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16625415332937337/50000000000000000000 : ℝ) ≤ ((9247359869731911853/9250000000000000000 : ℝ)+2*(69619964649/46250000000000 : ℝ)*(14757/100000 : ℝ))^(2143/512 : ℝ) := by
    rw [show (9247359869731911853/9250000000000000000 : ℝ)+2*(69619964649/46250000000000 : ℝ)*(14757/100000 : ℝ)=(10001588537302933/10000000000000000 : ℝ) by norm_num, show 1+2*(16625415332937337/50000000000000000000 : ℝ)=(25016625415332937337/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9247359869731911853/9250000000000000000 : ℝ)*(X 1 0+X 2 0)+(69619964649/46250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (11057/100000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (9247359869731911853/9250000000000000000 : ℝ)) (alpha := (69619964649/46250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9247359869731911853/9250000000000000000 : ℝ)*(X 0 1+X 2 1)+(69619964649/46250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (11057/100000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (9247359869731911853/9250000000000000000 : ℝ)) (alpha := (69619964649/46250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9247359869731911853/9250000000000000000 : ℝ)*(X 0 2+X 1 2)+(69619964649/46250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (11057/100000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (9247359869731911853/9250000000000000000 : ℝ)) (alpha := (69619964649/46250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-411389457/2000000000 : ℝ)*X 0 0+(270696107/500000000 : ℝ)*X 0 1+(5243729413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349364377/10000000000 : ℝ)*X 1 0+(-1071840729/5000000000 : ℝ)*X 1 1+(524372963/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349363777/10000000000 : ℝ)*X 2 0+(524372991/1000000000 : ℝ)*X 2 1+(-1071840943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2165262687/5000000000 : ℝ)*X 0 0+(207835179/500000000 : ℝ)*X 0 1+(2255586557/5000000000 : ℝ)*X 0 2+(2165262687/5000000000 : ℝ)*X 1 0+(207835179/500000000 : ℝ)*X 1 1+(2255586557/5000000000 : ℝ)*X 1 2+(2165262687/5000000000 : ℝ)*X 2 0+(207835179/500000000 : ℝ)*X 2 1+(2255586557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-64279987/312500000 : ℝ)*X 0 0+(5244341163/10000000000 : ℝ)*X 0 1+(5286433/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061120661/2000000000 : ℝ)*X 1 0+(-1974103639/10000000000 : ℝ)*X 1 1+(1082661511/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061120689/2000000000 : ℝ)*X 2 0+(2706653687/5000000000 : ℝ)*X 2 1+(-987051849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2165275873/5000000000 : ℝ)*X 0 0+(4509899403/10000000000 : ℝ)*X 0 1+(519747949/1250000000 : ℝ)*X 0 2+(2165275873/5000000000 : ℝ)*X 1 0+(4509899403/10000000000 : ℝ)*X 1 1+(519747949/1250000000 : ℝ)*X 1 2+(2165275873/5000000000 : ℝ)*X 2 0+(4509899403/10000000000 : ℝ)*X 2 1+(519747949/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4604462315697426456435996417/462500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2068691953/100000000000000 : ℝ)*(base19) + (1402838377/100000000000000 : ℝ)*(base23) + (22453467/12500000000000 : ℝ)*(upper2) + (160089287/25000000000000 : ℝ)*(upper3) + (91635307/50000000000000 : ℝ)*(upper4) + (4348464247148137/100000000000000 : ℝ)*(major0) + (4348464247148137/100000000000000 : ℝ)*(major1) + (4348464247148137/100000000000000 : ℝ)*(major2) + (2937874000764049/50000000000000 : ℝ)*(sp0) + (2937886855987167/50000000000000 : ℝ)*(sp1) + (5875774377827911/100000000000000 : ℝ)*(sp2) + (1410565551176251/50000000000000 : ℝ)*(sp3) + (27779138189/100000000000000 : ℝ)*(sp4) + (21279424339/100000000000000 : ℝ)*(sp7) + (70528809544421/2500000000000 : ℝ)*(f.failure) + (5875775780666287/100000000000000 : ℝ)*(f.sum) + (9246807431913/2312500000000000000000000000 : ℝ)*base65 + (6040453706499767861/925000000000000000000000000000000 : ℝ)*base67 + (2796835504450232139/925000000000000000000000000000000 : ℝ)*base70 + (1291465544699767861/925000000000000000000000000000000 : ℝ)*base71 + (8234091180299/4625000000000000000000000000 : ℝ)*base74 + (3989355901899767861/925000000000000000000000000000000 : ℝ)*base75 + (2766766610374767861/925000000000000000000000000000000 : ℝ)*base77 + (18852456690275232139/925000000000000000000000000000000 : ℝ)*base80 + (741080082607/144531250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5493/15625000000000000000 : ℝ)*base90 + (5493/15625000000000000000 : ℝ)*base92 + (5493/15625000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1597668441432899042383555911/231250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1435453613/100000000000000 : ℝ)*(base19) + (61332571/3125000000000 : ℝ)*(base23) + (6882487/4000000000000 : ℝ)*(upper2) + (29912747/12500000000000 : ℝ)*(upper3) + (111630701/50000000000000 : ℝ)*(upper5) + (2189981956374443/50000000000000 : ℝ)*(major0) + (2189981956374443/50000000000000 : ℝ)*(major1) + (2189981956374443/50000000000000 : ℝ)*(major2) + (30402859183/100000000000000 : ℝ)*(sp1) + (7213503957/20000000000000 : ℝ)*(sp2) + (295916959046837/5000000000000 : ℝ)*(sp4) + (1183661468524789/20000000000000 : ℝ)*(sp5) + (5918301150774683/100000000000000 : ℝ)*(sp6) + (1420794207133237/50000000000000 : ℝ)*(sp7) + (1420794207133237/50000000000000 : ℝ)*(f.failure) + (295916959046837/5000000000000 : ℝ)*(f.sum) + (2418787645809/578125000000000000000000000 : ℝ)*base66 + (785924720585627121/462500000000000000000000000000000 : ℝ)*base68 + (3642710004360627121/462500000000000000000000000000000 : ℝ)*base70 + (6389473977910627121/462500000000000000000000000000000 : ℝ)*base72 + (6035847879403/4625000000000000000000000000 : ℝ)*base73 + (3402540546173127121/462500000000000000000000000000000 : ℝ)*base76 + (3707782735010627121/462500000000000000000000000000000 : ℝ)*base78 + (2144126812635627121/462500000000000000000000000000000 : ℝ)*base80 + (1623405010717/289062500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4478229/312500000000000000000 : ℝ)*base89 + (4478229/312500000000000000000 : ℝ)*base91 + (4478229/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1327_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (347/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1327_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1327_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3233/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1219/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (347/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1327_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1327_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1327_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3233/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1219/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (347/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1327_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
