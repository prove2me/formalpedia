-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1604_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:39:49.459089+00:00
-- url     : https://prove2.me/submissions/cd5a9e8a-59c7-4bcf-a530-e83d023df797

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
theorem support_rectangle_w1604_s3_0 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1719363633/10000000000 : ℝ)*x 0 + (682747001/1250000000 : ℝ)*x 1 + (5179616367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1719363633/10000000000 : ℝ)^4735 ≤ (2644343486533/25000000000000 : ℝ)^3711 := by
    have hnat : (1719363633 : ℕ)^4735*25000000000000^3711 ≤ 2644343486533^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719363633 10000000000 2644343486533 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682747001/1250000000 : ℝ)^4735 ≤ (23112399577539/50000000000000 : ℝ)^3711 := by
    have hnat : (682747001 : ℕ)^4735*50000000000000^3711 ≤ 23112399577539^3711*1250000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682747001 1250000000 23112399577539 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179616367/10000000000 : ℝ)^4735 ≤ (8639565378537/20000000000000 : ℝ)^3711 := by
    have hnat : (5179616367 : ℕ)^4735*20000000000000^3711 ≤ 8639565378537^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179616367 10000000000 8639565378537 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1719363633/10000000000 : ℝ), (682747001/1250000000 : ℝ), (5179616367/10000000000 : ℝ)] ![(2644343486533/25000000000000 : ℝ), (23112399577539/50000000000000 : ℝ), (8639565378537/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1719363633/10000000000 : ℝ)|^4735 ≤ (2644343486533/25000000000000 : ℝ)^3711
        have hw : |(-1719363633/10000000000 : ℝ)|=(1719363633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682747001/1250000000 : ℝ)|^4735 ≤ (23112399577539/50000000000000 : ℝ)^3711
        have hw : |(682747001/1250000000 : ℝ)|=(682747001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179616367/10000000000 : ℝ)|^4735 ≤ (8639565378537/20000000000000 : ℝ)^3711
        have hw : |(5179616367/10000000000 : ℝ)|=(5179616367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s3_1 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338647281/2500000000 : ℝ)*x 0 + (-373004181/2000000000 : ℝ)*x 1 + (5179616683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338647281/2500000000 : ℝ)^4735 ≤ (45068366870301/100000000000000 : ℝ)^3711 := by
    have hnat : (1338647281 : ℕ)^4735*100000000000000^3711 ≤ 45068366870301^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338647281 2500000000 45068366870301 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373004181/2000000000 : ℝ)^4735 ≤ (1173380285581/10000000000000 : ℝ)^3711 := by
    have hnat : (373004181 : ℕ)^4735*10000000000000^3711 ≤ 1173380285581^3711*2000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373004181 2000000000 1173380285581 10000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179616683/10000000000 : ℝ)^4735 ≤ (1727913210213/4000000000000 : ℝ)^3711 := by
    have hnat : (5179616683 : ℕ)^4735*4000000000000^3711 ≤ 1727913210213^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179616683 10000000000 1727913210213 4000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338647281/2500000000 : ℝ), (-373004181/2000000000 : ℝ), (5179616683/10000000000 : ℝ)] ![(45068366870301/100000000000000 : ℝ), (1173380285581/10000000000000 : ℝ), (1727913210213/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338647281/2500000000 : ℝ)|^4735 ≤ (45068366870301/100000000000000 : ℝ)^3711
        have hw : |(1338647281/2500000000 : ℝ)|=(1338647281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-373004181/2000000000 : ℝ)|^4735 ≤ (1173380285581/10000000000000 : ℝ)^3711
        have hw : |(-373004181/2000000000 : ℝ)|=(373004181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179616683/10000000000 : ℝ)|^4735 ≤ (1727913210213/4000000000000 : ℝ)^3711
        have hw : |(5179616683/10000000000 : ℝ)|=(5179616683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s3_2 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677294757/5000000000 : ℝ)*x 0 + (647452027/1250000000 : ℝ)*x 1 + (-1865021003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677294757/5000000000 : ℝ)^4735 ≤ (9013674211723/20000000000000 : ℝ)^3711 := by
    have hnat : (2677294757 : ℕ)^4735*20000000000000^3711 ≤ 9013674211723^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677294757 5000000000 9013674211723 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647452027/1250000000 : ℝ)^4735 ≤ (43197825285853/100000000000000 : ℝ)^3711 := by
    have hnat : (647452027 : ℕ)^4735*100000000000000^3711 ≤ 43197825285853^3711*1250000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647452027 1250000000 43197825285853 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865021003/10000000000 : ℝ)^4735 ≤ (733362727657/6250000000000 : ℝ)^3711 := by
    have hnat : (1865021003 : ℕ)^4735*6250000000000^3711 ≤ 733362727657^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865021003 10000000000 733362727657 6250000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677294757/5000000000 : ℝ), (647452027/1250000000 : ℝ), (-1865021003/10000000000 : ℝ)] ![(9013674211723/20000000000000 : ℝ), (43197825285853/100000000000000 : ℝ), (733362727657/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677294757/5000000000 : ℝ)|^4735 ≤ (9013674211723/20000000000000 : ℝ)^3711
        have hw : |(2677294757/5000000000 : ℝ)|=(2677294757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647452027/1250000000 : ℝ)|^4735 ≤ (43197825285853/100000000000000 : ℝ)^3711
        have hw : |(647452027/1250000000 : ℝ)|=(647452027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1865021003/10000000000 : ℝ)|^4735 ≤ (733362727657/6250000000000 : ℝ)^3711
        have hw : |(-1865021003/10000000000 : ℝ)|=(1865021003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s3_3 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4217431347/10000000000 : ℝ)*x 0 + (1942078813/5000000000 : ℝ)*x 1 + (571567043/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4217431347/10000000000 : ℝ)^4735 ≤ (33234191703261/100000000000000 : ℝ)^3711 := by
    have hnat : (4217431347 : ℕ)^4735*100000000000000^3711 ≤ 33234191703261^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217431347 10000000000 33234191703261 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942078813/5000000000 : ℝ)^4735 ≤ (14960251631533/50000000000000 : ℝ)^3711 := by
    have hnat : (1942078813 : ℕ)^4735*50000000000000^3711 ≤ 14960251631533^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942078813 5000000000 14960251631533 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571567043/1250000000 : ℝ)^4735 ≤ (736906100377/2000000000000 : ℝ)^3711 := by
    have hnat : (571567043 : ℕ)^4735*2000000000000^3711 ≤ 736906100377^3711*1250000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571567043 1250000000 736906100377 2000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4217431347/10000000000 : ℝ), (1942078813/5000000000 : ℝ), (571567043/1250000000 : ℝ)] ![(33234191703261/100000000000000 : ℝ), (14960251631533/50000000000000 : ℝ), (736906100377/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4217431347/10000000000 : ℝ)|^4735 ≤ (33234191703261/100000000000000 : ℝ)^3711
        have hw : |(4217431347/10000000000 : ℝ)|=(4217431347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1942078813/5000000000 : ℝ)|^4735 ≤ (14960251631533/50000000000000 : ℝ)^3711
        have hw : |(1942078813/5000000000 : ℝ)|=(1942078813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571567043/1250000000 : ℝ)|^4735 ≤ (736906100377/2000000000000 : ℝ)^3711
        have hw : |(571567043/1250000000 : ℝ)|=(571567043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s3_4 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1719435389/10000000000 : ℝ)*x 0 + (2590859123/5000000000 : ℝ)*x 1 + (2729926149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1719435389/10000000000 : ℝ)^4735 ≤ (1057793719441/10000000000000 : ℝ)^3711 := by
    have hnat : (1719435389 : ℕ)^4735*10000000000000^3711 ≤ 1057793719441^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719435389 10000000000 1057793719441 10000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590859123/5000000000 : ℝ)^4735 ≤ (43220194800143/100000000000000 : ℝ)^3711 := by
    have hnat : (2590859123 : ℕ)^4735*100000000000000^3711 ≤ 43220194800143^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590859123 5000000000 43220194800143 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729926149/5000000000 : ℝ)^4735 ≤ (9240373597317/20000000000000 : ℝ)^3711 := by
    have hnat : (2729926149 : ℕ)^4735*20000000000000^3711 ≤ 9240373597317^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729926149 5000000000 9240373597317 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1719435389/10000000000 : ℝ), (2590859123/5000000000 : ℝ), (2729926149/5000000000 : ℝ)] ![(1057793719441/10000000000000 : ℝ), (43220194800143/100000000000000 : ℝ), (9240373597317/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1719435389/10000000000 : ℝ)|^4735 ≤ (1057793719441/10000000000000 : ℝ)^3711
        have hw : |(-1719435389/10000000000 : ℝ)|=(1719435389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590859123/5000000000 : ℝ)|^4735 ≤ (43220194800143/100000000000000 : ℝ)^3711
        have hw : |(2590859123/5000000000 : ℝ)|=(2590859123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729926149/5000000000 : ℝ)|^4735 ≤ (9240373597317/20000000000000 : ℝ)^3711
        have hw : |(2729926149/5000000000 : ℝ)|=(2729926149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s3_5 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279683907/10000000000 : ℝ)*x 0 + (-316956949/2000000000 : ℝ)*x 1 + (5459852267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279683907/10000000000 : ℝ)^4735 ≤ (44265497482567/100000000000000 : ℝ)^3711 := by
    have hnat : (5279683907 : ℕ)^4735*100000000000000^3711 ≤ 44265497482567^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279683907 10000000000 44265497482567 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316956949/2000000000 : ℝ)^4735 ≤ (9532634850117/100000000000000 : ℝ)^3711 := by
    have hnat : (316956949 : ℕ)^4735*100000000000000^3711 ≤ 9532634850117^3711*2000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316956949 2000000000 9532634850117 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459852267/10000000000 : ℝ)^4735 ≤ (23100933825937/50000000000000 : ℝ)^3711 := by
    have hnat : (5459852267 : ℕ)^4735*50000000000000^3711 ≤ 23100933825937^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459852267 10000000000 23100933825937 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279683907/10000000000 : ℝ), (-316956949/2000000000 : ℝ), (5459852267/10000000000 : ℝ)] ![(44265497482567/100000000000000 : ℝ), (9532634850117/100000000000000 : ℝ), (23100933825937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279683907/10000000000 : ℝ)|^4735 ≤ (44265497482567/100000000000000 : ℝ)^3711
        have hw : |(5279683907/10000000000 : ℝ)|=(5279683907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-316956949/2000000000 : ℝ)|^4735 ≤ (9532634850117/100000000000000 : ℝ)^3711
        have hw : |(-316956949/2000000000 : ℝ)|=(316956949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459852267/10000000000 : ℝ)|^4735 ≤ (23100933825937/50000000000000 : ℝ)^3711
        have hw : |(5459852267/10000000000 : ℝ)|=(5459852267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s3_6 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164990121/312500000 : ℝ)*x 0 + (5459852283/10000000000 : ℝ)*x 1 + (-1584784773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164990121/312500000 : ℝ)^4735 ≤ (44265497108151/100000000000000 : ℝ)^3711 := by
    have hnat : (164990121 : ℕ)^4735*100000000000000^3711 ≤ 44265497108151^3711*312500000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164990121 312500000 44265497108151 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459852283/10000000000 : ℝ)^4735 ≤ (11550466956157/25000000000000 : ℝ)^3711 := by
    have hnat : (5459852283 : ℕ)^4735*25000000000000^3711 ≤ 11550466956157^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459852283 10000000000 11550466956157 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584784773/10000000000 : ℝ)^4735 ≤ (4766317532507/50000000000000 : ℝ)^3711 := by
    have hnat : (1584784773 : ℕ)^4735*50000000000000^3711 ≤ 4766317532507^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584784773 10000000000 4766317532507 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164990121/312500000 : ℝ), (5459852283/10000000000 : ℝ), (-1584784773/10000000000 : ℝ)] ![(44265497108151/100000000000000 : ℝ), (11550466956157/25000000000000 : ℝ), (4766317532507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164990121/312500000 : ℝ)|^4735 ≤ (44265497108151/100000000000000 : ℝ)^3711
        have hw : |(164990121/312500000 : ℝ)|=(164990121/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459852283/10000000000 : ℝ)|^4735 ≤ (11550466956157/25000000000000 : ℝ)^3711
        have hw : |(5459852283/10000000000 : ℝ)|=(5459852283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1584784773/10000000000 : ℝ)|^4735 ≤ (4766317532507/50000000000000 : ℝ)^3711
        have hw : |(-1584784773/10000000000 : ℝ)|=(1584784773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s3_7 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4217607357/10000000000 : ℝ)*x 0 + (4567410789/10000000000 : ℝ)*x 1 + (1944668691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4217607357/10000000000 : ℝ)^4735 ≤ (33235961429017/100000000000000 : ℝ)^3711 := by
    have hnat : (4217607357 : ℕ)^4735*100000000000000^3711 ≤ 33235961429017^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217607357 10000000000 33235961429017 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4567410789/10000000000 : ℝ)^4735 ≤ (1471704603037/4000000000000 : ℝ)^3711 := by
    have hnat : (4567410789 : ℕ)^4735*4000000000000^3711 ≤ 1471704603037^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4567410789 10000000000 1471704603037 4000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1944668691/5000000000 : ℝ)^4735 ≤ (936606983773/3125000000000 : ℝ)^3711 := by
    have hnat : (1944668691 : ℕ)^4735*3125000000000^3711 ≤ 936606983773^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944668691 5000000000 936606983773 3125000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4217607357/10000000000 : ℝ), (4567410789/10000000000 : ℝ), (1944668691/5000000000 : ℝ)] ![(33235961429017/100000000000000 : ℝ), (1471704603037/4000000000000 : ℝ), (936606983773/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4217607357/10000000000 : ℝ)|^4735 ≤ (33235961429017/100000000000000 : ℝ)^3711
        have hw : |(4217607357/10000000000 : ℝ)|=(4217607357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4567410789/10000000000 : ℝ)|^4735 ≤ (1471704603037/4000000000000 : ℝ)^3711
        have hw : |(4567410789/10000000000 : ℝ)|=(4567410789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1944668691/5000000000 : ℝ)|^4735 ≤ (936606983773/3125000000000 : ℝ)^3711
        have hw : |(1944668691/5000000000 : ℝ)|=(1944668691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1604_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (413/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2561/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5191/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8183/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (413/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2561/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (413/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2561/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (413/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2561/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (413/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2561/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (413/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2561/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (413/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2561/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2561/25000 : ℝ) ^ (4731/1024 : ℝ) ≤ (1340366164495151/50000000000000000000 : ℝ) := by
    have hpowers : (2561/25000 : ℝ)^4731 ≤ (1340366164495151/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2561 : ℕ)^4731*50000000000000000000^1024 ≤ 1340366164495151^1024*25000^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2561 25000 1340366164495151 50000000000000000000 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2561/25000 : ℝ)) (X := (1340366164495151/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (413/2500 : ℝ) ^ (4731/1024 : ℝ) ≤ (2438455077159781/10000000000000000000 : ℝ) := by
    have hpowers : (413/2500 : ℝ)^4731 ≤ (2438455077159781/10000000000000000000 : ℝ)^1024 := by
      have hnat : (413 : ℕ)^4731*10000000000000000000^1024 ≤ 2438455077159781^1024*2500^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        413 2500 2438455077159781 10000000000000000000 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (413/2500 : ℝ)) (X := (2438455077159781/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001340366164495151/25000000000000000000 : ℝ) ≤ (250002901090939/250000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (25001340366164495151/25000000000000000000 : ℝ)^1024 ≤ (250002901090939/250000000000000 : ℝ)^4731 := by
      have hnat : (25001340366164495151 : ℕ)^1024*250000000000000^4731 ≤ 250002901090939^4731*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001340366164495151 25000000000000000000 250002901090939 250000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250002901090939/250000000000000 : ℝ)) (X := (25001340366164495151/25000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251691580193786757/6250000000000000000 : ℝ) ≤ (5000292875836013/5000000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (6251691580193786757/6250000000000000000 : ℝ)^1024 ≤ (5000292875836013/5000000000000000 : ℝ)^4731 := by
      have hnat : (6251691580193786757 : ℕ)^1024*5000000000000000^4731 ≤ 5000292875836013^4731*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251691580193786757 6250000000000000000 5000292875836013 5000000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000292875836013/5000000000000000 : ℝ)) (X := (6251691580193786757/6250000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002438455077159781/5000000000000000000 : ℝ) ≤ (2500263864926623/2500000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (5002438455077159781/5000000000000000000 : ℝ)^1024 ≤ (2500263864926623/2500000000000000 : ℝ)^4731 := by
      have hnat : (5002438455077159781 : ℕ)^1024*2500000000000000^4731 ≤ 2500263864926623^4731*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002438455077159781 5000000000000000000 2500263864926623 2500000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500263864926623/2500000000000000 : ℝ)) (X := (5002438455077159781/5000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1340366164495151/50000000000000000000 : ℝ) ≤ ((1307314685659566399/1307500000000000000 : ℝ)+2*(78284672411/104600000000000 : ℝ)*(2561/25000 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (1307314685659566399/1307500000000000000 : ℝ)+2*(78284672411/104600000000000 : ℝ)*(2561/25000 : ℝ)=(250002901090939/250000000000000 : ℝ) by norm_num, show 1+2*(1340366164495151/50000000000000000000 : ℝ)=(25001340366164495151/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2438455077159781/10000000000000000000 : ℝ)+(1340366164495151/50000000000000000000 : ℝ) ≤ ((1307314685659566399/1307500000000000000 : ℝ)+(78284672411/104600000000000 : ℝ)*((413/2500 : ℝ)+(2561/25000 : ℝ)))^(4731/1024 : ℝ) := by
    rw [show (1307314685659566399/1307500000000000000 : ℝ)+(78284672411/104600000000000 : ℝ)*((413/2500 : ℝ)+(2561/25000 : ℝ))=(5000292875836013/5000000000000000 : ℝ) by norm_num, show 1+(2438455077159781/10000000000000000000 : ℝ)+(1340366164495151/50000000000000000000 : ℝ)=(6251691580193786757/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2438455077159781/10000000000000000000 : ℝ) ≤ ((1307314685659566399/1307500000000000000 : ℝ)+2*(78284672411/104600000000000 : ℝ)*(413/2500 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (1307314685659566399/1307500000000000000 : ℝ)+2*(78284672411/104600000000000 : ℝ)*(413/2500 : ℝ)=(2500263864926623/2500000000000000 : ℝ) by norm_num, show 1+2*(2438455077159781/10000000000000000000 : ℝ)=(5002438455077159781/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1307314685659566399/1307500000000000000 : ℝ)*(X 1 0+X 2 0)+(78284672411/104600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (2561/25000 : ℝ)) (hi := (413/2500 : ℝ)) (c := (1307314685659566399/1307500000000000000 : ℝ)) (alpha := (78284672411/104600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1307314685659566399/1307500000000000000 : ℝ)*(X 0 1+X 2 1)+(78284672411/104600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (2561/25000 : ℝ)) (hi := (413/2500 : ℝ)) (c := (1307314685659566399/1307500000000000000 : ℝ)) (alpha := (78284672411/104600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1307314685659566399/1307500000000000000 : ℝ)*(X 0 2+X 1 2)+(78284672411/104600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (2561/25000 : ℝ)) (hi := (413/2500 : ℝ)) (c := (1307314685659566399/1307500000000000000 : ℝ)) (alpha := (78284672411/104600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1719363633/10000000000 : ℝ)*X 0 0+(682747001/1250000000 : ℝ)*X 0 1+(5179616367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338647281/2500000000 : ℝ)*X 1 0+(-373004181/2000000000 : ℝ)*X 1 1+(5179616683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677294757/5000000000 : ℝ)*X 2 0+(647452027/1250000000 : ℝ)*X 2 1+(-1865021003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4217431347/10000000000 : ℝ)*X 0 0+(1942078813/5000000000 : ℝ)*X 0 1+(571567043/1250000000 : ℝ)*X 0 2+(4217431347/10000000000 : ℝ)*X 1 0+(1942078813/5000000000 : ℝ)*X 1 1+(571567043/1250000000 : ℝ)*X 1 2+(4217431347/10000000000 : ℝ)*X 2 0+(1942078813/5000000000 : ℝ)*X 2 1+(571567043/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1719435389/10000000000 : ℝ)*X 0 0+(2590859123/5000000000 : ℝ)*X 0 1+(2729926149/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279683907/10000000000 : ℝ)*X 1 0+(-316956949/2000000000 : ℝ)*X 1 1+(5459852267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((164990121/312500000 : ℝ)*X 2 0+(5459852283/10000000000 : ℝ)*X 2 1+(-1584784773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4217607357/10000000000 : ℝ)*X 0 0+(4567410789/10000000000 : ℝ)*X 0 1+(1944668691/5000000000 : ℝ)*X 0 2+(4217607357/10000000000 : ℝ)*X 1 0+(4567410789/10000000000 : ℝ)*X 1 1+(1944668691/5000000000 : ℝ)*X 1 2+(4217607357/10000000000 : ℝ)*X 2 0+(4567410789/10000000000 : ℝ)*X 2 1+(1944668691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (277495532337752260617148881/65375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (325195879/50000000000000 : ℝ)*(base19) + (332912653/50000000000000 : ℝ)*(base23) + (58883091/20000000000000 : ℝ)*(upper3) + (64929043/50000000000000 : ℝ)*(upper4) + (46387481/50000000000000 : ℝ)*(upper5) + (312143371317817/12500000000000 : ℝ)*(major0) + (312143371317817/12500000000000 : ℝ)*(major1) + (2497146970542537/100000000000000 : ℝ)*(major2) + (1770794391215451/50000000000000 : ℝ)*(sp0) + (3541592807123263/100000000000000 : ℝ)*(sp1) + (1770796395844857/50000000000000 : ℝ)*(sp2) + (1452693245430863/100000000000000 : ℝ)*(sp3) + (2337542059/50000000000000 : ℝ)*(sp4) + (443540629/6250000000000 : ℝ)*(sp7) + (1452700342080927/100000000000000 : ℝ)*(f.failure) + (177079672875751/5000000000000 : ℝ)*(f.sum) + (52014396168143/10460000000000000000000000000 : ℝ)*base65 + (100685007623453659/32687500000000000000000000000000 : ℝ)*base68 + (220132887594385737/130750000000000000000000000000000 : ℝ)*base70 + (133030390427233841/32687500000000000000000000000000 : ℝ)*base71 + (41571192020263/10460000000000000000000000000 : ℝ)*base73 + (2471755158947635737/130750000000000000000000000000000 : ℝ)*base76 + (181032988394275267/16343750000000000000000000000000 : ℝ)*base78 + (21170056972994017/16343750000000000000000000000000 : ℝ)*base80 + (8345434755839/1307500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (9268429/2500000000000000000000 : ℝ)*base89 + (9268429/2500000000000000000000 : ℝ)*base91 + (15731571/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27314800840669680177599511/4085937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (16149527/1562500000000 : ℝ)*(base19) + (1086211149/100000000000000 : ℝ)*(base23) + (132601709/100000000000000 : ℝ)*(upper3) + (19991631/50000000000000 : ℝ)*(lower4) + (31525169/20000000000000 : ℝ)*(upper5) + (39610584957753/1562500000000 : ℝ)*(major0) + (39610584957753/1562500000000 : ℝ)*(major1) + (39610584957753/1562500000000 : ℝ)*(major2) + (11615531059/100000000000000 : ℝ)*(sp1) + (2917002837/25000000000000 : ℝ)*(sp2) + (359538848708753/10000000000000 : ℝ)*(sp4) + (449421979748343/12500000000000 : ℝ)*(sp5) + (449421966608129/12500000000000 : ℝ)*(sp6) + (368691541167249/25000000000000 : ℝ)*(sp7) + (368691541167249/25000000000000 : ℝ)*(f.failure) + (359538848708753/10000000000000 : ℝ)*(f.sum) + (6711597315887/1307500000000000000000000000 : ℝ)*base66 + (3834148314808553/2042968750000000000000000000000 : ℝ)*base68 + (1991756146650411/1021484375000000000000000000000 : ℝ)*base69 + (6499945654089803/2042968750000000000000000000000 : ℝ)*base72 + (11990657797479/2615000000000000000000000000 : ℝ)*base74 + (15543744038593913/8171875000000000000000000000000 : ℝ)*base75 + (3435399649525411/1021484375000000000000000000000 : ℝ)*base77 + (18442320054681661/1021484375000000000000000000000 : ℝ)*base79 + (598480087531/653750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (3491523/625000000000000000000 : ℝ)*base89 + (3491523/625000000000000000000 : ℝ)*base91 + (3491523/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1604_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (413/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2561/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1604_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1604_s4_0 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-429874431/2500000000 : ℝ)*x 0 + (5461307369/10000000000 : ℝ)*x 1 + (2590097969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429874431/2500000000 : ℝ)^4735 ≤ (10578426497871/100000000000000 : ℝ)^3711 := by
    have hnat : (429874431 : ℕ)^4735*100000000000000^3711 ≤ 10578426497871^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429874431 2500000000 10578426497871 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461307369/10000000000 : ℝ)^4735 ≤ (23108789565527/50000000000000 : ℝ)^3711 := by
    have hnat : (5461307369 : ℕ)^4735*50000000000000^3711 ≤ 23108789565527^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461307369 10000000000 23108789565527 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590097969/5000000000 : ℝ)^4735 ≤ (8640798871513/20000000000000 : ℝ)^3711 := by
    have hnat : (2590097969 : ℕ)^4735*20000000000000^3711 ≤ 8640798871513^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590097969 5000000000 8640798871513 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429874431/2500000000 : ℝ), (5461307369/10000000000 : ℝ), (2590097969/5000000000 : ℝ)] ![(10578426497871/100000000000000 : ℝ), (23108789565527/50000000000000 : ℝ), (8640798871513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429874431/2500000000 : ℝ)|^4735 ≤ (10578426497871/100000000000000 : ℝ)^3711
        have hw : |(-429874431/2500000000 : ℝ)|=(429874431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461307369/10000000000 : ℝ)|^4735 ≤ (23108789565527/50000000000000 : ℝ)^3711
        have hw : |(5461307369/10000000000 : ℝ)|=(5461307369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590097969/5000000000 : ℝ)|^4735 ≤ (8640798871513/20000000000000 : ℝ)^3711
        have hw : |(2590097969/5000000000 : ℝ)|=(2590097969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s4_1 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070882203/2000000000 : ℝ)*x 0 + (-186449133/1000000000 : ℝ)*x 1 + (5180195909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070882203/2000000000 : ℝ)^4735 ≤ (9013290823743/20000000000000 : ℝ)^3711 := by
    have hnat : (1070882203 : ℕ)^4735*20000000000000^3711 ≤ 9013290823743^3711*2000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070882203 2000000000 9013290823743 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186449133/1000000000 : ℝ)^4735 ≤ (293238795547/2500000000000 : ℝ)^3711 := by
    have hnat : (186449133 : ℕ)^4735*2500000000000^3711 ≤ 293238795547^3711*1000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186449133 1000000000 293238795547 2500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180195909/10000000000 : ℝ)^4735 ≤ (43203994048959/100000000000000 : ℝ)^3711 := by
    have hnat : (5180195909 : ℕ)^4735*100000000000000^3711 ≤ 43203994048959^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180195909 10000000000 43203994048959 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070882203/2000000000 : ℝ), (-186449133/1000000000 : ℝ), (5180195909/10000000000 : ℝ)] ![(9013290823743/20000000000000 : ℝ), (293238795547/2500000000000 : ℝ), (43203994048959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070882203/2000000000 : ℝ)|^4735 ≤ (9013290823743/20000000000000 : ℝ)^3711
        have hw : |(1070882203/2000000000 : ℝ)|=(1070882203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-186449133/1000000000 : ℝ)|^4735 ≤ (293238795547/2500000000000 : ℝ)^3711
        have hw : |(-186449133/1000000000 : ℝ)|=(186449133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180195909/10000000000 : ℝ)|^4735 ≤ (43203994048959/100000000000000 : ℝ)^3711
        have hw : |(5180195909/10000000000 : ℝ)|=(5180195909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s4_2 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338602727/2500000000 : ℝ)*x 0 + (5180196097/10000000000 : ℝ)*x 1 + (-1864491223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338602727/2500000000 : ℝ)^4735 ≤ (5633306621203/12500000000000 : ℝ)^3711 := by
    have hnat : (1338602727 : ℕ)^4735*12500000000000^3711 ≤ 5633306621203^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338602727 2500000000 5633306621203 12500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180196097/10000000000 : ℝ)^4735 ≤ (43203996049579/100000000000000 : ℝ)^3711 := by
    have hnat : (5180196097 : ℕ)^4735*100000000000000^3711 ≤ 43203996049579^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180196097 10000000000 43203996049579 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1864491223/10000000000 : ℝ)^4735 ≤ (11729550962997/100000000000000 : ℝ)^3711 := by
    have hnat : (1864491223 : ℕ)^4735*100000000000000^3711 ≤ 11729550962997^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864491223 10000000000 11729550962997 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338602727/2500000000 : ℝ), (5180196097/10000000000 : ℝ), (-1864491223/10000000000 : ℝ)] ![(5633306621203/12500000000000 : ℝ), (43203996049579/100000000000000 : ℝ), (11729550962997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338602727/2500000000 : ℝ)|^4735 ≤ (5633306621203/12500000000000 : ℝ)^3711
        have hw : |(1338602727/2500000000 : ℝ)|=(1338602727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180196097/10000000000 : ℝ)|^4735 ≤ (43203996049579/100000000000000 : ℝ)^3711
        have hw : |(5180196097/10000000000 : ℝ)|=(5180196097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1864491223/10000000000 : ℝ)|^4735 ≤ (11729550962997/100000000000000 : ℝ)^3711
        have hw : |(-1864491223/10000000000 : ℝ)|=(1864491223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s4_3 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054379573/2500000000 : ℝ)*x 0 + (388567153/1000000000 : ℝ)*x 1 + (571375489/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054379573/2500000000 : ℝ)^4735 ≤ (33235065905621/100000000000000 : ℝ)^3711 := by
    have hnat : (1054379573 : ℕ)^4735*100000000000000^3711 ≤ 33235065905621^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054379573 2500000000 33235065905621 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388567153/1000000000 : ℝ)^4735 ≤ (3741922992829/12500000000000 : ℝ)^3711 := by
    have hnat : (388567153 : ℕ)^4735*12500000000000^3711 ≤ 3741922992829^3711*1000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388567153 1000000000 3741922992829 12500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571375489/1250000000 : ℝ)^4735 ≤ (36829550137091/100000000000000 : ℝ)^3711 := by
    have hnat : (571375489 : ℕ)^4735*100000000000000^3711 ≤ 36829550137091^3711*1250000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571375489 1250000000 36829550137091 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054379573/2500000000 : ℝ), (388567153/1000000000 : ℝ), (571375489/1250000000 : ℝ)] ![(33235065905621/100000000000000 : ℝ), (3741922992829/12500000000000 : ℝ), (36829550137091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054379573/2500000000 : ℝ)|^4735 ≤ (33235065905621/100000000000000 : ℝ)^3711
        have hw : |(1054379573/2500000000 : ℝ)|=(1054379573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388567153/1000000000 : ℝ)|^4735 ≤ (3741922992829/12500000000000 : ℝ)^3711
        have hw : |(388567153/1000000000 : ℝ)|=(388567153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571375489/1250000000 : ℝ)|^4735 ≤ (36829550137091/100000000000000 : ℝ)^3711
        have hw : |(571375489/1250000000 : ℝ)|=(571375489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s4_4 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-53736529/312500000 : ℝ)*x 0 + (2591139853/5000000000 : ℝ)*x 1 + (2729600889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53736529/312500000 : ℝ)^4735 ≤ (10578985425231/100000000000000 : ℝ)^3711 := by
    have hnat : (53736529 : ℕ)^4735*100000000000000^3711 ≤ 10578985425231^3711*312500000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53736529 312500000 10578985425231 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591139853/5000000000 : ℝ)^4735 ≤ (8645234040813/20000000000000 : ℝ)^3711 := by
    have hnat : (2591139853 : ℕ)^4735*20000000000000^3711 ≤ 8645234040813^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591139853 5000000000 8645234040813 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729600889/5000000000 : ℝ)^4735 ≤ (1847793774549/4000000000000 : ℝ)^3711 := by
    have hnat : (2729600889 : ℕ)^4735*4000000000000^3711 ≤ 1847793774549^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729600889 5000000000 1847793774549 4000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53736529/312500000 : ℝ), (2591139853/5000000000 : ℝ), (2729600889/5000000000 : ℝ)] ![(10578985425231/100000000000000 : ℝ), (8645234040813/20000000000000 : ℝ), (1847793774549/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53736529/312500000 : ℝ)|^4735 ≤ (10578985425231/100000000000000 : ℝ)^3711
        have hw : |(-53736529/312500000 : ℝ)|=(53736529/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591139853/5000000000 : ℝ)|^4735 ≤ (8645234040813/20000000000000 : ℝ)^3711
        have hw : |(2591139853/5000000000 : ℝ)|=(2591139853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729600889/5000000000 : ℝ)|^4735 ≤ (1847793774549/4000000000000 : ℝ)^3711
        have hw : |(2729600889/5000000000 : ℝ)|=(2729600889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s4_5 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639918811/5000000000 : ℝ)*x 0 + (-1585485547/10000000000 : ℝ)*x 1 + (2729600889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639918811/5000000000 : ℝ)^4735 ≤ (2213357093557/5000000000000 : ℝ)^3711 := by
    have hnat : (2639918811 : ℕ)^4735*5000000000000^3711 ≤ 2213357093557^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639918811 5000000000 2213357093557 5000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1585485547/10000000000 : ℝ)^4735 ≤ (1192251718857/12500000000000 : ℝ)^3711 := by
    have hnat : (1585485547 : ℕ)^4735*12500000000000^3711 ≤ 1192251718857^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585485547 10000000000 1192251718857 12500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729600889/5000000000 : ℝ)^4735 ≤ (1847793774549/4000000000000 : ℝ)^3711 := by
    have hnat : (2729600889 : ℕ)^4735*4000000000000^3711 ≤ 1847793774549^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729600889 5000000000 1847793774549 4000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639918811/5000000000 : ℝ), (-1585485547/10000000000 : ℝ), (2729600889/5000000000 : ℝ)] ![(2213357093557/5000000000000 : ℝ), (1192251718857/12500000000000 : ℝ), (1847793774549/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639918811/5000000000 : ℝ)|^4735 ≤ (2213357093557/5000000000000 : ℝ)^3711
        have hw : |(2639918811/5000000000 : ℝ)|=(2639918811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1585485547/10000000000 : ℝ)|^4735 ≤ (1192251718857/12500000000000 : ℝ)^3711
        have hw : |(-1585485547/10000000000 : ℝ)|=(1585485547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729600889/5000000000 : ℝ)|^4735 ≤ (1847793774549/4000000000000 : ℝ)^3711
        have hw : |(2729600889/5000000000 : ℝ)|=(2729600889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s4_6 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639918811/5000000000 : ℝ)*x 0 + (2729600889/5000000000 : ℝ)*x 1 + (-1585485547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639918811/5000000000 : ℝ)^4735 ≤ (2213357093557/5000000000000 : ℝ)^3711 := by
    have hnat : (2639918811 : ℕ)^4735*5000000000000^3711 ≤ 2213357093557^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639918811 5000000000 2213357093557 5000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729600889/5000000000 : ℝ)^4735 ≤ (1847793774549/4000000000000 : ℝ)^3711 := by
    have hnat : (2729600889 : ℕ)^4735*4000000000000^3711 ≤ 1847793774549^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729600889 5000000000 1847793774549 4000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1585485547/10000000000 : ℝ)^4735 ≤ (1192251718857/12500000000000 : ℝ)^3711 := by
    have hnat : (1585485547 : ℕ)^4735*12500000000000^3711 ≤ 1192251718857^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585485547 10000000000 1192251718857 12500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639918811/5000000000 : ℝ), (2729600889/5000000000 : ℝ), (-1585485547/10000000000 : ℝ)] ![(2213357093557/5000000000000 : ℝ), (1847793774549/4000000000000 : ℝ), (1192251718857/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639918811/5000000000 : ℝ)|^4735 ≤ (2213357093557/5000000000000 : ℝ)^3711
        have hw : |(2639918811/5000000000 : ℝ)|=(2639918811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729600889/5000000000 : ℝ)|^4735 ≤ (1847793774549/4000000000000 : ℝ)^3711
        have hw : |(2729600889/5000000000 : ℝ)|=(2729600889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1585485547/10000000000 : ℝ)|^4735 ≤ (1192251718857/12500000000000 : ℝ)^3711
        have hw : |(-1585485547/10000000000 : ℝ)|=(1585485547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s4_7 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (843538399/2000000000 : ℝ)*x 0 + (456592389/1000000000 : ℝ)*x 1 + (3890805003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (843538399/2000000000 : ℝ)^4735 ≤ (16618406222507/50000000000000 : ℝ)^3711 := by
    have hnat : (843538399 : ℕ)^4735*50000000000000^3711 ≤ 16618406222507^3711*2000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843538399 2000000000 16618406222507 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456592389/1000000000 : ℝ)^4735 ≤ (9194333256857/25000000000000 : ℝ)^3711 := by
    have hnat : (456592389 : ℕ)^4735*25000000000000^3711 ≤ 9194333256857^3711*1000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456592389 1000000000 9194333256857 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3890805003/10000000000 : ℝ)^4735 ≤ (7496463627489/25000000000000 : ℝ)^3711 := by
    have hnat : (3890805003 : ℕ)^4735*25000000000000^3711 ≤ 7496463627489^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3890805003 10000000000 7496463627489 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(843538399/2000000000 : ℝ), (456592389/1000000000 : ℝ), (3890805003/10000000000 : ℝ)] ![(16618406222507/50000000000000 : ℝ), (9194333256857/25000000000000 : ℝ), (7496463627489/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(843538399/2000000000 : ℝ)|^4735 ≤ (16618406222507/50000000000000 : ℝ)^3711
        have hw : |(843538399/2000000000 : ℝ)|=(843538399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(456592389/1000000000 : ℝ)|^4735 ≤ (9194333256857/25000000000000 : ℝ)^3711
        have hw : |(456592389/1000000000 : ℝ)|=(456592389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3890805003/10000000000 : ℝ)|^4735 ≤ (7496463627489/25000000000000 : ℝ)^3711
        have hw : |(3890805003/10000000000 : ℝ)|=(3890805003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1604_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5197/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (511/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8183/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5191/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8183/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5191/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8183/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5191/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8183/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5191/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8183/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5191/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8183/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5191/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5191/50000 : ℝ) ^ (4731/1024 : ℝ) ≤ (2851694866444329/100000000000000000000 : ℝ) := by
    have hpowers : (5191/50000 : ℝ)^4731 ≤ (2851694866444329/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5191 : ℕ)^4731*100000000000000000000^1024 ≤ 2851694866444329^1024*50000^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5191 50000 2851694866444329 100000000000000000000 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5191/50000 : ℝ)) (X := (2851694866444329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8183/50000 : ℝ) ^ (4731/1024 : ℝ) ≤ (4670382452886123/20000000000000000000 : ℝ) := by
    have hpowers : (8183/50000 : ℝ)^4731 ≤ (4670382452886123/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8183 : ℕ)^4731*20000000000000000000^1024 ≤ 4670382452886123^1024*50000^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8183 50000 4670382452886123 20000000000000000000 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8183/50000 : ℝ)) (X := (4670382452886123/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002851694866444329/50000000000000000000 : ℝ) ≤ (10000123444104679/10000000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (50002851694866444329/50000000000000000000 : ℝ)^1024 ≤ (10000123444104679/10000000000000000 : ℝ)^4731 := by
      have hnat : (50002851694866444329 : ℕ)^1024*10000000000000000^4731 ≤ 10000123444104679^4731*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002851694866444329 50000000000000000000 10000123444104679 10000000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000123444104679/10000000000000000 : ℝ)) (X := (50002851694866444329/50000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1562909431361419921/1562500000000000000 : ℝ) ≤ (2500141776260361/2500000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (1562909431361419921/1562500000000000000 : ℝ)^1024 ≤ (2500141776260361/2500000000000000 : ℝ)^4731 := by
      have hnat : (1562909431361419921 : ℕ)^1024*2500000000000000^4731 ≤ 2500141776260361^4731*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562909431361419921 1562500000000000000 2500141776260361 2500000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500141776260361/2500000000000000 : ℝ)) (X := (1562909431361419921/1562500000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004670382452886123/10000000000000000000 : ℝ) ≤ (10001010765978209/10000000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (10004670382452886123/10000000000000000000 : ℝ)^1024 ≤ (10001010765978209/10000000000000000 : ℝ)^4731 := by
      have hnat : (10004670382452886123 : ℕ)^1024*10000000000000000^4731 ≤ 10001010765978209^4731*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004670382452886123 10000000000000000000 10001010765978209 10000000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001010765978209/10000000000000000 : ℝ)) (X := (10004670382452886123/10000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2851694866444329/100000000000000000000 : ℝ) ≤ ((14957881628457852669/14960000000000000000 : ℝ)+2*(88732187353/119680000000000 : ℝ)*(5191/50000 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (14957881628457852669/14960000000000000000 : ℝ)+2*(88732187353/119680000000000 : ℝ)*(5191/50000 : ℝ)=(10000123444104679/10000000000000000 : ℝ) by norm_num, show 1+2*(2851694866444329/100000000000000000000 : ℝ)=(50002851694866444329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4670382452886123/20000000000000000000 : ℝ)+(2851694866444329/100000000000000000000 : ℝ) ≤ ((14957881628457852669/14960000000000000000 : ℝ)+(88732187353/119680000000000 : ℝ)*((8183/50000 : ℝ)+(5191/50000 : ℝ)))^(4731/1024 : ℝ) := by
    rw [show (14957881628457852669/14960000000000000000 : ℝ)+(88732187353/119680000000000 : ℝ)*((8183/50000 : ℝ)+(5191/50000 : ℝ))=(2500141776260361/2500000000000000 : ℝ) by norm_num, show 1+(4670382452886123/20000000000000000000 : ℝ)+(2851694866444329/100000000000000000000 : ℝ)=(1562909431361419921/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4670382452886123/20000000000000000000 : ℝ) ≤ ((14957881628457852669/14960000000000000000 : ℝ)+2*(88732187353/119680000000000 : ℝ)*(8183/50000 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (14957881628457852669/14960000000000000000 : ℝ)+2*(88732187353/119680000000000 : ℝ)*(8183/50000 : ℝ)=(10001010765978209/10000000000000000 : ℝ) by norm_num, show 1+2*(4670382452886123/20000000000000000000 : ℝ)=(10004670382452886123/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14957881628457852669/14960000000000000000 : ℝ)*(X 1 0+X 2 0)+(88732187353/119680000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (5191/50000 : ℝ)) (hi := (8183/50000 : ℝ)) (c := (14957881628457852669/14960000000000000000 : ℝ)) (alpha := (88732187353/119680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14957881628457852669/14960000000000000000 : ℝ)*(X 0 1+X 2 1)+(88732187353/119680000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (5191/50000 : ℝ)) (hi := (8183/50000 : ℝ)) (c := (14957881628457852669/14960000000000000000 : ℝ)) (alpha := (88732187353/119680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14957881628457852669/14960000000000000000 : ℝ)*(X 0 2+X 1 2)+(88732187353/119680000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (5191/50000 : ℝ)) (hi := (8183/50000 : ℝ)) (c := (14957881628457852669/14960000000000000000 : ℝ)) (alpha := (88732187353/119680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-429874431/2500000000 : ℝ)*X 0 0+(5461307369/10000000000 : ℝ)*X 0 1+(2590097969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070882203/2000000000 : ℝ)*X 1 0+(-186449133/1000000000 : ℝ)*X 1 1+(5180195909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338602727/2500000000 : ℝ)*X 2 0+(5180196097/10000000000 : ℝ)*X 2 1+(-1864491223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1054379573/2500000000 : ℝ)*X 0 0+(388567153/1000000000 : ℝ)*X 0 1+(571375489/1250000000 : ℝ)*X 0 2+(1054379573/2500000000 : ℝ)*X 1 0+(388567153/1000000000 : ℝ)*X 1 1+(571375489/1250000000 : ℝ)*X 1 2+(1054379573/2500000000 : ℝ)*X 2 0+(388567153/1000000000 : ℝ)*X 2 1+(571375489/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-53736529/312500000 : ℝ)*X 0 0+(2591139853/5000000000 : ℝ)*X 0 1+(2729600889/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639918811/5000000000 : ℝ)*X 1 0+(-1585485547/10000000000 : ℝ)*X 1 1+(2729600889/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639918811/5000000000 : ℝ)*X 2 0+(2729600889/5000000000 : ℝ)*X 2 1+(-1585485547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((843538399/2000000000 : ℝ)*X 0 0+(456592389/1000000000 : ℝ)*X 0 1+(3890805003/10000000000 : ℝ)*X 0 2+(843538399/2000000000 : ℝ)*X 1 0+(456592389/1000000000 : ℝ)*X 1 1+(3890805003/10000000000 : ℝ)*X 1 2+(843538399/2000000000 : ℝ)*X 2 0+(456592389/1000000000 : ℝ)*X 2 1+(3890805003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9133182002473631572168347/1000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (420894277/25000000000000 : ℝ)*(base19) + (386257429/25000000000000 : ℝ)*(base23) + (36120339/100000000000000 : ℝ)*(lower2) + (203619327/100000000000000 : ℝ)*(upper3) + (27856137/12500000000000 : ℝ)*(upper5) + (627064228302127/25000000000000 : ℝ)*(major0) + (627064228302127/25000000000000 : ℝ)*(major1) + (627064228302127/25000000000000 : ℝ)*(major2) + (3557328621198007/100000000000000 : ℝ)*(sp0) + (1778674176750147/50000000000000 : ℝ)*(sp1) + (1778674246023843/50000000000000 : ℝ)*(sp2) + (729577362707683/50000000000000 : ℝ)*(sp3) + (4283175879/20000000000000 : ℝ)*(sp4) + (2189871211/25000000000000 : ℝ)*(sp7) + (145916348490021/10000000000000 : ℝ)*(f.failure) + (1778675018538701/50000000000000 : ℝ)*(f.sum) + (448793703643/136000000000000000000000000 : ℝ)*base66 + (21410842034745633/34000000000000000000000000000000 : ℝ)*base67 + (363935692603254367/34000000000000000000000000000000 : ℝ)*base70 + (127873381911254367/34000000000000000000000000000000 : ℝ)*base72 + (373936324699/136000000000000000000000000 : ℝ)*base74 + (79574563183254367/34000000000000000000000000000000 : ℝ)*base76 + (235830878163254367/34000000000000000000000000000000 : ℝ)*base78 + (73573299008745633/34000000000000000000000000000000 : ℝ)*base79 + (9956723887/27200000000000000000000000 : ℝ)*base82 + (311233/250000000000000000000 : ℝ)*base90 + (311233/250000000000000000000 : ℝ)*base92 + (311233/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (561673275560533700690421993/93500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (927250031/100000000000000 : ℝ)*(base19) + (125508723/12500000000000 : ℝ)*(base23) + (4605699/1562500000000 : ℝ)*(lower1) + (126280793/100000000000000 : ℝ)*(upper3) + (8639251/25000000000000 : ℝ)*(lower4) + (124557343/100000000000000 : ℝ)*(upper5) + (318270585213333/12500000000000 : ℝ)*(major0) + (318270585213333/12500000000000 : ℝ)*(major1) + (318270585213333/12500000000000 : ℝ)*(major2) + (804923453/100000000000000 : ℝ)*(sp2) + (90277826506491/2500000000000 : ℝ)*(sp4) + (3611112133009609/100000000000000 : ℝ)*(sp5) + (3611111251266403/100000000000000 : ℝ)*(sp6) + (370304025728413/25000000000000 : ℝ)*(sp7) + (370304025728413/25000000000000 : ℝ)*(f.failure) + (90277826506491/2500000000000 : ℝ)*(f.sum) + (1834562487811/748000000000000000000000000 : ℝ)*base66 + (1621579328797939223/187000000000000000000000000000000 : ℝ)*base68 + (1246500106169939223/187000000000000000000000000000000 : ℝ)*base70 + (2164723337963939223/187000000000000000000000000000000 : ℝ)*base72 + (287829639887/748000000000000000000000000 : ℝ)*base74 + (1641863899103939223/187000000000000000000000000000000 : ℝ)*base76 + (3074764296867939223/187000000000000000000000000000000 : ℝ)*base78 + (2399641754542939223/187000000000000000000000000000000 : ℝ)*base80 + (4366416846541/748000000000000000000000000 : ℝ)*base81 + (10611751/625000000000000000000 : ℝ)*base89 + (10611751/625000000000000000000 : ℝ)*base91 + (10611751/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1604_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5197/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (511/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1604_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1604_s5_0 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1719510859/10000000000 : ℝ)*x 0 + (5461248177/10000000000 : ℝ)*x 1 + (518024631/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1719510859/10000000000 : ℝ)^4735 ≤ (5289264801353/50000000000000 : ℝ)^3711 := by
    have hnat : (1719510859 : ℕ)^4735*50000000000000^3711 ≤ 5289264801353^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719510859 10000000000 5289264801353 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461248177/10000000000 : ℝ)^4735 ≤ (4621693998227/10000000000000 : ℝ)^3711 := by
    have hnat : (5461248177 : ℕ)^4735*10000000000000^3711 ≤ 4621693998227^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461248177 10000000000 4621693998227 10000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518024631/1000000000 : ℝ)^4735 ≤ (5400566299591/12500000000000 : ℝ)^3711 := by
    have hnat : (518024631 : ℕ)^4735*12500000000000^3711 ≤ 5400566299591^3711*1000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518024631 1000000000 5400566299591 12500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1719510859/10000000000 : ℝ), (5461248177/10000000000 : ℝ), (518024631/1000000000 : ℝ)] ![(5289264801353/50000000000000 : ℝ), (4621693998227/10000000000000 : ℝ), (5400566299591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1719510859/10000000000 : ℝ)|^4735 ≤ (5289264801353/50000000000000 : ℝ)^3711
        have hw : |(-1719510859/10000000000 : ℝ)|=(1719510859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461248177/10000000000 : ℝ)|^4735 ≤ (4621693998227/10000000000000 : ℝ)^3711
        have hw : |(5461248177/10000000000 : ℝ)|=(5461248177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518024631/1000000000 : ℝ)|^4735 ≤ (5400566299591/12500000000000 : ℝ)^3711
        have hw : |(518024631/1000000000 : ℝ)|=(518024631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s5_1 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354394463/10000000000 : ℝ)*x 0 + (-1864446939/10000000000 : ℝ)*x 1 + (323765381/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354394463/10000000000 : ℝ)^4735 ≤ (45066276364051/100000000000000 : ℝ)^3711 := by
    have hnat : (5354394463 : ℕ)^4735*100000000000000^3711 ≤ 45066276364051^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354394463 10000000000 45066276364051 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1864446939/10000000000 : ℝ)^4735 ≤ (2345839099821/20000000000000 : ℝ)^3711 := by
    have hnat : (1864446939 : ℕ)^4735*20000000000000^3711 ≤ 2345839099821^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864446939 10000000000 2345839099821 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323765381/625000000 : ℝ)^4735 ≤ (2160226405971/5000000000000 : ℝ)^3711 := by
    have hnat : (323765381 : ℕ)^4735*5000000000000^3711 ≤ 2160226405971^3711*625000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323765381 625000000 2160226405971 5000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354394463/10000000000 : ℝ), (-1864446939/10000000000 : ℝ), (323765381/625000000 : ℝ)] ![(45066276364051/100000000000000 : ℝ), (2345839099821/20000000000000 : ℝ), (2160226405971/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354394463/10000000000 : ℝ)|^4735 ≤ (45066276364051/100000000000000 : ℝ)^3711
        have hw : |(5354394463/10000000000 : ℝ)|=(5354394463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1864446939/10000000000 : ℝ)|^4735 ≤ (2345839099821/20000000000000 : ℝ)^3711
        have hw : |(-1864446939/10000000000 : ℝ)|=(1864446939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323765381/625000000 : ℝ)|^4735 ≤ (2160226405971/5000000000000 : ℝ)^3711
        have hw : |(323765381/625000000 : ℝ)|=(323765381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s5_2 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354394909/10000000000 : ℝ)*x 0 + (5180246373/10000000000 : ℝ)*x 1 + (-74577839/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354394909/10000000000 : ℝ)^4735 ≤ (45066281153717/100000000000000 : ℝ)^3711 := by
    have hnat : (5354394909 : ℕ)^4735*100000000000000^3711 ≤ 45066281153717^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354394909 10000000000 45066281153717 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180246373/10000000000 : ℝ)^4735 ≤ (864090621343/2000000000000 : ℝ)^3711 := by
    have hnat : (5180246373 : ℕ)^4735*2000000000000^3711 ≤ 864090621343^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180246373 10000000000 864090621343 2000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74577839/400000000 : ℝ)^4735 ≤ (2345837552237/20000000000000 : ℝ)^3711 := by
    have hnat : (74577839 : ℕ)^4735*20000000000000^3711 ≤ 2345837552237^3711*400000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74577839 400000000 2345837552237 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354394909/10000000000 : ℝ), (5180246373/10000000000 : ℝ), (-74577839/400000000 : ℝ)] ![(45066281153717/100000000000000 : ℝ), (864090621343/2000000000000 : ℝ), (2345837552237/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354394909/10000000000 : ℝ)|^4735 ≤ (45066281153717/100000000000000 : ℝ)^3711
        have hw : |(5354394909/10000000000 : ℝ)|=(5354394909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180246373/10000000000 : ℝ)|^4735 ≤ (864090621343/2000000000000 : ℝ)^3711
        have hw : |(5180246373/10000000000 : ℝ)|=(5180246373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-74577839/400000000 : ℝ)|^4735 ≤ (2345837552237/20000000000000 : ℝ)^3711
        have hw : |(-74577839/400000000 : ℝ)|=(74577839/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s5_3 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2108762319/5000000000 : ℝ)*x 0 + (3885804181/10000000000 : ℝ)*x 1 + (1142717717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108762319/5000000000 : ℝ)^4735 ≤ (6647025942537/20000000000000 : ℝ)^3711 := by
    have hnat : (2108762319 : ℕ)^4735*20000000000000^3711 ≤ 6647025942537^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108762319 5000000000 6647025942537 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3885804181/10000000000 : ℝ)^4735 ≤ (1871042993179/6250000000000 : ℝ)^3711 := by
    have hnat : (3885804181 : ℕ)^4735*6250000000000^3711 ≤ 1871042993179^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3885804181 10000000000 1871042993179 6250000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142717717/2500000000 : ℝ)^4735 ≤ (36828182384961/100000000000000 : ℝ)^3711 := by
    have hnat : (1142717717 : ℕ)^4735*100000000000000^3711 ≤ 36828182384961^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142717717 2500000000 36828182384961 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2108762319/5000000000 : ℝ), (3885804181/10000000000 : ℝ), (1142717717/2500000000 : ℝ)] ![(6647025942537/20000000000000 : ℝ), (1871042993179/6250000000000 : ℝ), (36828182384961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2108762319/5000000000 : ℝ)|^4735 ≤ (6647025942537/20000000000000 : ℝ)^3711
        have hw : |(2108762319/5000000000 : ℝ)|=(2108762319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3885804181/10000000000 : ℝ)|^4735 ≤ (1871042993179/6250000000000 : ℝ)^3711
        have hw : |(3885804181/10000000000 : ℝ)|=(3885804181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1142717717/2500000000 : ℝ)|^4735 ≤ (36828182384961/100000000000000 : ℝ)^3711
        have hw : |(1142717717/2500000000 : ℝ)|=(1142717717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s5_4 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1719581371/10000000000 : ℝ)*x 0 + (5182328241/10000000000 : ℝ)*x 1 + (682393111/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1719581371/10000000000 : ℝ)^4735 ≤ (2644770774809/25000000000000 : ℝ)^3711 := by
    have hnat : (1719581371 : ℕ)^4735*25000000000000^3711 ≤ 2644770774809^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719581371 10000000000 2644770774809 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182328241/10000000000 : ℝ)^4735 ≤ (21613343375943/50000000000000 : ℝ)^3711 := by
    have hnat : (5182328241 : ℕ)^4735*50000000000000^3711 ≤ 21613343375943^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182328241 10000000000 21613343375943 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682393111/1250000000 : ℝ)^4735 ≤ (11548557534253/25000000000000 : ℝ)^3711 := by
    have hnat : (682393111 : ℕ)^4735*25000000000000^3711 ≤ 11548557534253^3711*1250000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682393111 1250000000 11548557534253 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1719581371/10000000000 : ℝ), (5182328241/10000000000 : ℝ), (682393111/1250000000 : ℝ)] ![(2644770774809/25000000000000 : ℝ), (21613343375943/50000000000000 : ℝ), (11548557534253/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1719581371/10000000000 : ℝ)|^4735 ≤ (2644770774809/25000000000000 : ℝ)^3711
        have hw : |(-1719581371/10000000000 : ℝ)|=(1719581371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182328241/10000000000 : ℝ)|^4735 ≤ (21613343375943/50000000000000 : ℝ)^3711
        have hw : |(5182328241/10000000000 : ℝ)|=(5182328241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682393111/1250000000 : ℝ)|^4735 ≤ (11548557534253/25000000000000 : ℝ)^3711
        have hw : |(682393111/1250000000 : ℝ)|=(682393111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s5_5 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279850741/10000000000 : ℝ)*x 0 + (-63421893/400000000 : ℝ)*x 1 + (5459144859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279850741/10000000000 : ℝ)^4735 ≤ (44267282214163/100000000000000 : ℝ)^3711 := by
    have hnat : (5279850741 : ℕ)^4735*100000000000000^3711 ≤ 44267282214163^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279850741 10000000000 44267282214163 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63421893/400000000 : ℝ)^4735 ≤ (2384621987527/25000000000000 : ℝ)^3711 := by
    have hnat : (63421893 : ℕ)^4735*25000000000000^3711 ≤ 2384621987527^3711*400000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63421893 400000000 2384621987527 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459144859/10000000000 : ℝ)^4735 ≤ (46194229823907/100000000000000 : ℝ)^3711 := by
    have hnat : (5459144859 : ℕ)^4735*100000000000000^3711 ≤ 46194229823907^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459144859 10000000000 46194229823907 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279850741/10000000000 : ℝ), (-63421893/400000000 : ℝ), (5459144859/10000000000 : ℝ)] ![(44267282214163/100000000000000 : ℝ), (2384621987527/25000000000000 : ℝ), (46194229823907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279850741/10000000000 : ℝ)|^4735 ≤ (44267282214163/100000000000000 : ℝ)^3711
        have hw : |(5279850741/10000000000 : ℝ)|=(5279850741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-63421893/400000000 : ℝ)|^4735 ≤ (2384621987527/25000000000000 : ℝ)^3711
        have hw : |(-63421893/400000000 : ℝ)|=(63421893/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459144859/10000000000 : ℝ)|^4735 ≤ (46194229823907/100000000000000 : ℝ)^3711
        have hw : |(5459144859/10000000000 : ℝ)|=(5459144859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s5_6 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319962707/2500000000 : ℝ)*x 0 + (1364786203/2500000000 : ℝ)*x 1 + (-1585547269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319962707/2500000000 : ℝ)^4735 ≤ (22133641572431/50000000000000 : ℝ)^3711 := by
    have hnat : (1319962707 : ℕ)^4735*50000000000000^3711 ≤ 22133641572431^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319962707 2500000000 22133641572431 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364786203/2500000000 : ℝ)^4735 ≤ (46194229316461/100000000000000 : ℝ)^3711 := by
    have hnat : (1364786203 : ℕ)^4735*100000000000000^3711 ≤ 46194229316461^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364786203 2500000000 46194229316461 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1585547269/10000000000 : ℝ)^4735 ≤ (4769243760129/50000000000000 : ℝ)^3711 := by
    have hnat : (1585547269 : ℕ)^4735*50000000000000^3711 ≤ 4769243760129^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585547269 10000000000 4769243760129 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319962707/2500000000 : ℝ), (1364786203/2500000000 : ℝ), (-1585547269/10000000000 : ℝ)] ![(22133641572431/50000000000000 : ℝ), (46194229316461/100000000000000 : ℝ), (4769243760129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319962707/2500000000 : ℝ)|^4735 ≤ (22133641572431/50000000000000 : ℝ)^3711
        have hw : |(1319962707/2500000000 : ℝ)|=(1319962707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364786203/2500000000 : ℝ)|^4735 ≤ (46194229316461/100000000000000 : ℝ)^3711
        have hw : |(1364786203/2500000000 : ℝ)|=(1364786203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1585547269/10000000000 : ℝ)|^4735 ≤ (4769243760129/50000000000000 : ℝ)^3711
        have hw : |(-1585547269/10000000000 : ℝ)|=(1585547269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s5_7 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (421769949/1000000000 : ℝ)*x 0 + (45657943/100000000 : ℝ)*x 1 + (1945466389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421769949/1000000000 : ℝ)^4735 ≤ (1329475512231/4000000000000 : ℝ)^3711 := by
    have hnat : (421769949 : ℕ)^4735*4000000000000^3711 ≤ 1329475512231^3711*1000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421769949 1000000000 1329475512231 4000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45657943/100000000 : ℝ)^4735 ≤ (18388000596277/50000000000000 : ℝ)^3711 := by
    have hnat : (45657943 : ℕ)^4735*50000000000000^3711 ≤ 18388000596277^3711*100000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45657943 100000000 18388000596277 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945466389/5000000000 : ℝ)^4735 ≤ (3748388873119/12500000000000 : ℝ)^3711 := by
    have hnat : (1945466389 : ℕ)^4735*12500000000000^3711 ≤ 3748388873119^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945466389 5000000000 3748388873119 12500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(421769949/1000000000 : ℝ), (45657943/100000000 : ℝ), (1945466389/5000000000 : ℝ)] ![(1329475512231/4000000000000 : ℝ), (18388000596277/50000000000000 : ℝ), (3748388873119/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(421769949/1000000000 : ℝ)|^4735 ≤ (1329475512231/4000000000000 : ℝ)^3711
        have hw : |(421769949/1000000000 : ℝ)|=(421769949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45657943/100000000 : ℝ)|^4735 ≤ (18388000596277/50000000000000 : ℝ)^3711
        have hw : |(45657943/100000000 : ℝ)|=(45657943/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1945466389/5000000000 : ℝ)|^4735 ≤ (3748388873119/12500000000000 : ℝ)^3711
        have hw : |(1945466389/5000000000 : ℝ)|=(1945466389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1604_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5197/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2079/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16351/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (511/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5197/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (511/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5197/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (511/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5197/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (511/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5197/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (511/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5197/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (511/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5197/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5197/50000 : ℝ) ^ (4731/1024 : ℝ) ≤ (11199043862031/390625000000000000 : ℝ) := by
    have hpowers : (5197/50000 : ℝ)^4731 ≤ (11199043862031/390625000000000000 : ℝ)^1024 := by
      have hnat : (5197 : ℕ)^4731*390625000000000000^1024 ≤ 11199043862031^1024*50000^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5197 50000 11199043862031 390625000000000000 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5197/50000 : ℝ)) (X := (11199043862031/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (511/3125 : ℝ) ^ (4731/1024 : ℝ) ≤ (4651952744887397/20000000000000000000 : ℝ) := by
    have hpowers : (511/3125 : ℝ)^4731 ≤ (4651952744887397/20000000000000000000 : ℝ)^1024 := by
      have hnat : (511 : ℕ)^4731*20000000000000000000^1024 ≤ 4651952744887397^1024*3125^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        511 3125 4651952744887397 20000000000000000000 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (511/3125 : ℝ)) (X := (4651952744887397/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (195323699043862031/195312500000000000 : ℝ) ≤ (2000024820936013/2000000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (195323699043862031/195312500000000000 : ℝ)^1024 ≤ (2000024820936013/2000000000000000 : ℝ)^4731 := by
      have hnat : (195323699043862031 : ℕ)^1024*2000000000000000^4731 ≤ 2000024820936013^4731*195312500000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195323699043862031 195312500000000000 2000024820936013 2000000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000024820936013/2000000000000000 : ℝ)) (X := (195323699043862031/195312500000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026126718953116921/100000000000000000000 : ℝ) ≤ (5000282720589249/5000000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (100026126718953116921/100000000000000000000 : ℝ)^1024 ≤ (5000282720589249/5000000000000000 : ℝ)^4731 := by
      have hnat : (100026126718953116921 : ℕ)^1024*5000000000000000^4731 ≤ 5000282720589249^4731*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026126718953116921 100000000000000000000 5000282720589249 5000000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000282720589249/5000000000000000 : ℝ)) (X := (100026126718953116921/100000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004651952744887397/10000000000000000000 : ℝ) ≤ (10001006777676931/10000000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (10004651952744887397/10000000000000000000 : ℝ)^1024 ≤ (10001006777676931/10000000000000000 : ℝ)^4731 := by
      have hnat : (10004651952744887397 : ℕ)^1024*10000000000000000^4731 ≤ 10001006777676931^4731*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004651952744887397 10000000000000000000 10001006777676931 10000000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001006777676931/10000000000000000 : ℝ)) (X := (10004651952744887397/10000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(11199043862031/390625000000000000 : ℝ) ≤ ((29785782456277201033/29790000000000000000 : ℝ)+2*(441336498433/595800000000000 : ℝ)*(5197/50000 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (29785782456277201033/29790000000000000000 : ℝ)+2*(441336498433/595800000000000 : ℝ)*(5197/50000 : ℝ)=(2000024820936013/2000000000000000 : ℝ) by norm_num, show 1+2*(11199043862031/390625000000000000 : ℝ)=(195323699043862031/195312500000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4651952744887397/20000000000000000000 : ℝ)+(11199043862031/390625000000000000 : ℝ) ≤ ((29785782456277201033/29790000000000000000 : ℝ)+(441336498433/595800000000000 : ℝ)*((511/3125 : ℝ)+(5197/50000 : ℝ)))^(4731/1024 : ℝ) := by
    rw [show (29785782456277201033/29790000000000000000 : ℝ)+(441336498433/595800000000000 : ℝ)*((511/3125 : ℝ)+(5197/50000 : ℝ))=(5000282720589249/5000000000000000 : ℝ) by norm_num, show 1+(4651952744887397/20000000000000000000 : ℝ)+(11199043862031/390625000000000000 : ℝ)=(100026126718953116921/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4651952744887397/20000000000000000000 : ℝ) ≤ ((29785782456277201033/29790000000000000000 : ℝ)+2*(441336498433/595800000000000 : ℝ)*(511/3125 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (29785782456277201033/29790000000000000000 : ℝ)+2*(441336498433/595800000000000 : ℝ)*(511/3125 : ℝ)=(10001006777676931/10000000000000000 : ℝ) by norm_num, show 1+2*(4651952744887397/20000000000000000000 : ℝ)=(10004651952744887397/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29785782456277201033/29790000000000000000 : ℝ)*(X 1 0+X 2 0)+(441336498433/595800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (5197/50000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (29785782456277201033/29790000000000000000 : ℝ)) (alpha := (441336498433/595800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29785782456277201033/29790000000000000000 : ℝ)*(X 0 1+X 2 1)+(441336498433/595800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (5197/50000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (29785782456277201033/29790000000000000000 : ℝ)) (alpha := (441336498433/595800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29785782456277201033/29790000000000000000 : ℝ)*(X 0 2+X 1 2)+(441336498433/595800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (5197/50000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (29785782456277201033/29790000000000000000 : ℝ)) (alpha := (441336498433/595800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1719510859/10000000000 : ℝ)*X 0 0+(5461248177/10000000000 : ℝ)*X 0 1+(518024631/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354394463/10000000000 : ℝ)*X 1 0+(-1864446939/10000000000 : ℝ)*X 1 1+(323765381/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354394909/10000000000 : ℝ)*X 2 0+(5180246373/10000000000 : ℝ)*X 2 1+(-74577839/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2108762319/5000000000 : ℝ)*X 0 0+(3885804181/10000000000 : ℝ)*X 0 1+(1142717717/2500000000 : ℝ)*X 0 2+(2108762319/5000000000 : ℝ)*X 1 0+(3885804181/10000000000 : ℝ)*X 1 1+(1142717717/2500000000 : ℝ)*X 1 2+(2108762319/5000000000 : ℝ)*X 2 0+(3885804181/10000000000 : ℝ)*X 2 1+(1142717717/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1719581371/10000000000 : ℝ)*X 0 0+(5182328241/10000000000 : ℝ)*X 0 1+(682393111/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279850741/10000000000 : ℝ)*X 1 0+(-63421893/400000000 : ℝ)*X 1 1+(5459144859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319962707/2500000000 : ℝ)*X 2 0+(1364786203/2500000000 : ℝ)*X 2 1+(-1585547269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((421769949/1000000000 : ℝ)*X 0 0+(45657943/100000000 : ℝ)*X 0 1+(1945466389/5000000000 : ℝ)*X 0 2+(421769949/1000000000 : ℝ)*X 1 0+(45657943/100000000 : ℝ)*X 1 1+(1945466389/5000000000 : ℝ)*X 1 2+(421769949/1000000000 : ℝ)*X 2 0+(45657943/100000000 : ℝ)*X 2 1+(1945466389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2676448184881283375851397563/248250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1657821083/100000000000000 : ℝ)*(base19) + (128094763/10000000000000 : ℝ)*(base23) + (32369403/25000000000000 : ℝ)*(upper3) + (180255971/50000000000000 : ℝ)*(upper4) + (53346171/12500000000000 : ℝ)*(upper5) + (1254612831318589/50000000000000 : ℝ)*(major0) + (1254612831318589/50000000000000 : ℝ)*(major1) + (1254612831318589/50000000000000 : ℝ)*(major2) + (35587026404419/1000000000000 : ℝ)*(sp0) + (3558722258981001/100000000000000 : ℝ)*(sp1) + (1779361317927227/50000000000000 : ℝ)*(sp2) + (729859800646131/50000000000000 : ℝ)*(sp3) + (21276360183/100000000000000 : ℝ)*(sp4) + (7447804617/100000000000000 : ℝ)*(sp7) + (18246588113711/1250000000000 : ℝ)*(f.failure) + (889680979200521/25000000000000 : ℝ)*(f.sum) + (43305704496401/7447500000000000000000000000 : ℝ)*base65 + (739242321462417479/496500000000000000000000000000000 : ℝ)*base67 + (2789665200964082521/496500000000000000000000000000000 : ℝ)*base70 + (3772748576046417479/496500000000000000000000000000000 : ℝ)*base71 + (2694779473187/3723750000000000000000000000 : ℝ)*base74 + (4702599561892082521/496500000000000000000000000000000 : ℝ)*base76 + (999310884826917479/496500000000000000000000000000000 : ℝ)*base77 + (644335880248917479/496500000000000000000000000000000 : ℝ)*base79 + (40052866754197/14895000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (201397/31250000000000000000 : ℝ)*base89 + (201397/31250000000000000000 : ℝ)*base91 + (201397/31250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (400095023446153162488884303/49650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1363367867/100000000000000 : ℝ)*(base19) + (1544340959/100000000000000 : ℝ)*(base23) + (27765181/6250000000000 : ℝ)*(lower1) + (328733/200000000000 : ℝ)*(upper3) + (54367067/100000000000000 : ℝ)*(lower4) + (206775131/100000000000000 : ℝ)*(upper5) + (254713133310809/10000000000000 : ℝ)*(major0) + (254713133310809/10000000000000 : ℝ)*(major1) + (254713133310809/10000000000000 : ℝ)*(major2) + (163584891/12500000000000 : ℝ)*(sp2) + (451560493876299/12500000000000 : ℝ)*(sp4) + (144499303505701/4000000000000 : ℝ)*(sp5) + (112890034312197/3125000000000 : ℝ)*(sp6) + (1481778446595497/100000000000000 : ℝ)*(sp7) + (1481778446595497/100000000000000 : ℝ)*(f.failure) + (451560493876299/12500000000000 : ℝ)*(f.sum) + (204752492129/595800000000000000000000000 : ℝ)*base66 + (253645236126971899/99300000000000000000000000000000 : ℝ)*base67 + (37128617559971899/99300000000000000000000000000000 : ℝ)*base69 + (219326164815071899/99300000000000000000000000000000 : ℝ)*base71 + (171353741821/93093750000000000000000000 : ℝ)*base73 + (696296626675271899/99300000000000000000000000000000 : ℝ)*base75 + (90864200057628101/99300000000000000000000000000000 : ℝ)*base78 + (44714038289028101/99300000000000000000000000000000 : ℝ)*base80 + (5231774125187/2979000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (15255819/2500000000000000000000 : ℝ)*base89 + (15255819/2500000000000000000000 : ℝ)*base91 + (15255819/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1604_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5197/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2079/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16351/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1604_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1604_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (413/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2561/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2079/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16351/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1604_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1604_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1604_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (413/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2561/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2079/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16351/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1604_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
