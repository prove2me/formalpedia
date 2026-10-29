-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1636_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:01:41.356994+00:00
-- url     : https://prove2.me/submissions/5975e0b4-ddac-4018-86b1-b513f0171f80

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
theorem support_rectangle_w1636_s6_0 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-102561231/625000000 : ℝ)*x 0 + (5451496673/10000000000 : ℝ)*x 1 + (5183101053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102561231/625000000 : ℝ)^4863 ≤ (5066556377879/50000000000000 : ℝ)^3839 := by
    have hnat : (102561231 : ℕ)^4863*50000000000000^3839 ≤ 5066556377879^3839*625000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102561231 625000000 5066556377879 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451496673/10000000000 : ℝ)^4863 ≤ (46369774382681/100000000000000 : ℝ)^3839 := by
    have hnat : (5451496673 : ℕ)^4863*100000000000000^3839 ≤ 46369774382681^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451496673 10000000000 46369774382681 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183101053/10000000000 : ℝ)^4863 ≤ (2174855641861/5000000000000 : ℝ)^3839 := by
    have hnat : (5183101053 : ℕ)^4863*5000000000000^3839 ≤ 2174855641861^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183101053 10000000000 2174855641861 5000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102561231/625000000 : ℝ), (5451496673/10000000000 : ℝ), (5183101053/10000000000 : ℝ)] ![(5066556377879/50000000000000 : ℝ), (46369774382681/100000000000000 : ℝ), (2174855641861/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102561231/625000000 : ℝ)|^4863 ≤ (5066556377879/50000000000000 : ℝ)^3839
        have hw : |(-102561231/625000000 : ℝ)|=(102561231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451496673/10000000000 : ℝ)|^4863 ≤ (46369774382681/100000000000000 : ℝ)^3839
        have hw : |(5451496673/10000000000 : ℝ)|=(5451496673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183101053/10000000000 : ℝ)|^4863 ≤ (2174855641861/5000000000000 : ℝ)^3839
        have hw : |(5183101053/10000000000 : ℝ)|=(5183101053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s6_1 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53497783/100000000 : ℝ)*x 0 + (-1779218391/10000000000 : ℝ)*x 1 + (5183102481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53497783/100000000 : ℝ)^4863 ≤ (2263826440293/5000000000000 : ℝ)^3839 := by
    have hnat : (53497783 : ℕ)^4863*5000000000000^3839 ≤ 2263826440293^3839*100000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53497783 100000000 2263826440293 5000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1779218391/10000000000 : ℝ)^4863 ≤ (5613171586069/50000000000000 : ℝ)^3839 := by
    have hnat : (1779218391 : ℕ)^4863*50000000000000^3839 ≤ 5613171586069^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779218391 10000000000 5613171586069 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183102481/10000000000 : ℝ)^4863 ≤ (43497128017687/100000000000000 : ℝ)^3839 := by
    have hnat : (5183102481 : ℕ)^4863*100000000000000^3839 ≤ 43497128017687^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183102481 10000000000 43497128017687 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53497783/100000000 : ℝ), (-1779218391/10000000000 : ℝ), (5183102481/10000000000 : ℝ)] ![(2263826440293/5000000000000 : ℝ), (5613171586069/50000000000000 : ℝ), (43497128017687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53497783/100000000 : ℝ)|^4863 ≤ (2263826440293/5000000000000 : ℝ)^3839
        have hw : |(53497783/100000000 : ℝ)|=(53497783/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1779218391/10000000000 : ℝ)|^4863 ≤ (5613171586069/50000000000000 : ℝ)^3839
        have hw : |(-1779218391/10000000000 : ℝ)|=(1779218391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183102481/10000000000 : ℝ)|^4863 ≤ (43497128017687/100000000000000 : ℝ)^3839
        have hw : |(5183102481/10000000000 : ℝ)|=(5183102481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s6_2 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674889371/5000000000 : ℝ)*x 0 + (5183102293/10000000000 : ℝ)*x 1 + (-889609023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674889371/5000000000 : ℝ)^4863 ≤ (45276533544413/100000000000000 : ℝ)^3839 := by
    have hnat : (2674889371 : ℕ)^4863*100000000000000^3839 ≤ 45276533544413^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674889371 5000000000 45276533544413 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183102293/10000000000 : ℝ)^4863 ≤ (21748563009569/50000000000000 : ℝ)^3839 := by
    have hnat : (5183102293 : ℕ)^4863*50000000000000^3839 ≤ 21748563009569^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183102293 10000000000 21748563009569 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (889609023/5000000000 : ℝ)^4863 ≤ (2245268082929/20000000000000 : ℝ)^3839 := by
    have hnat : (889609023 : ℕ)^4863*20000000000000^3839 ≤ 2245268082929^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889609023 5000000000 2245268082929 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674889371/5000000000 : ℝ), (5183102293/10000000000 : ℝ), (-889609023/5000000000 : ℝ)] ![(45276533544413/100000000000000 : ℝ), (21748563009569/50000000000000 : ℝ), (2245268082929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674889371/5000000000 : ℝ)|^4863 ≤ (45276533544413/100000000000000 : ℝ)^3839
        have hw : |(2674889371/5000000000 : ℝ)|=(2674889371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183102293/10000000000 : ℝ)|^4863 ≤ (21748563009569/50000000000000 : ℝ)^3839
        have hw : |(5183102293/10000000000 : ℝ)|=(5183102293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-889609023/5000000000 : ℝ)|^4863 ≤ (2245268082929/20000000000000 : ℝ)^3839
        have hw : |(-889609023/5000000000 : ℝ)|=(889609023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s6_3 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (838324193/2000000000 : ℝ)*x 0 + (772161687/2000000000 : ℝ)*x 1 + (454298243/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838324193/2000000000 : ℝ)^4863 ≤ (4154967721817/12500000000000 : ℝ)^3839 := by
    have hnat : (838324193 : ℕ)^4863*12500000000000^3839 ≤ 4154967721817^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838324193 2000000000 4154967721817 12500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772161687/2000000000 : ℝ)^4863 ≤ (14976158057463/50000000000000 : ℝ)^3839 := by
    have hnat : (772161687 : ℕ)^4863*50000000000000^3839 ≤ 14976158057463^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772161687 2000000000 14976158057463 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454298243/1000000000 : ℝ)^4863 ≤ (36807942103431/100000000000000 : ℝ)^3839 := by
    have hnat : (454298243 : ℕ)^4863*100000000000000^3839 ≤ 36807942103431^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454298243 1000000000 36807942103431 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838324193/2000000000 : ℝ), (772161687/2000000000 : ℝ), (454298243/1000000000 : ℝ)] ![(4154967721817/12500000000000 : ℝ), (14976158057463/50000000000000 : ℝ), (36807942103431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838324193/2000000000 : ℝ)|^4863 ≤ (4154967721817/12500000000000 : ℝ)^3839
        have hw : |(838324193/2000000000 : ℝ)|=(838324193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772161687/2000000000 : ℝ)|^4863 ≤ (14976158057463/50000000000000 : ℝ)^3839
        have hw : |(772161687/2000000000 : ℝ)|=(772161687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(454298243/1000000000 : ℝ)|^4863 ≤ (36807942103431/100000000000000 : ℝ)^3839
        have hw : |(454298243/1000000000 : ℝ)|=(454298243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s6_4 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-820522941/5000000000 : ℝ)*x 0 + (1296279527/2500000000 : ℝ)*x 1 + (2724729173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (820522941/5000000000 : ℝ)^4863 ≤ (2533407618747/25000000000000 : ℝ)^3839 := by
    have hnat : (820522941 : ℕ)^4863*25000000000000^3839 ≤ 2533407618747^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820522941 5000000000 2533407618747 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296279527/2500000000 : ℝ)^4863 ≤ (43518556412199/100000000000000 : ℝ)^3839 := by
    have hnat : (1296279527 : ℕ)^4863*100000000000000^3839 ≤ 43518556412199^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296279527 2500000000 43518556412199 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724729173/5000000000 : ℝ)^4863 ≤ (5793476638229/12500000000000 : ℝ)^3839 := by
    have hnat : (2724729173 : ℕ)^4863*12500000000000^3839 ≤ 5793476638229^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724729173 5000000000 5793476638229 12500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-820522941/5000000000 : ℝ), (1296279527/2500000000 : ℝ), (2724729173/5000000000 : ℝ)] ![(2533407618747/25000000000000 : ℝ), (43518556412199/100000000000000 : ℝ), (5793476638229/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-820522941/5000000000 : ℝ)|^4863 ≤ (2533407618747/25000000000000 : ℝ)^3839
        have hw : |(-820522941/5000000000 : ℝ)|=(820522941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296279527/2500000000 : ℝ)|^4863 ≤ (43518556412199/100000000000000 : ℝ)^3839
        have hw : |(1296279527/2500000000 : ℝ)|=(1296279527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724729173/5000000000 : ℝ)|^4863 ≤ (5793476638229/12500000000000 : ℝ)^3839
        have hw : |(2724729173/5000000000 : ℝ)|=(2724729173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s6_5 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639102367/5000000000 : ℝ)*x 0 + (-1512862511/10000000000 : ℝ)*x 1 + (1362364611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639102367/5000000000 : ℝ)^4863 ≤ (22255291543481/50000000000000 : ℝ)^3839 := by
    have hnat : (2639102367 : ℕ)^4863*50000000000000^3839 ≤ 22255291543481^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639102367 5000000000 22255291543481 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512862511/10000000000 : ℝ)^4863 ≤ (9141602732967/100000000000000 : ℝ)^3839 := by
    have hnat : (1512862511 : ℕ)^4863*100000000000000^3839 ≤ 9141602732967^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512862511 10000000000 9141602732967 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362364611/2500000000 : ℝ)^4863 ≤ (2896738385103/6250000000000 : ℝ)^3839 := by
    have hnat : (1362364611 : ℕ)^4863*6250000000000^3839 ≤ 2896738385103^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362364611 2500000000 2896738385103 6250000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639102367/5000000000 : ℝ), (-1512862511/10000000000 : ℝ), (1362364611/2500000000 : ℝ)] ![(22255291543481/50000000000000 : ℝ), (9141602732967/100000000000000 : ℝ), (2896738385103/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639102367/5000000000 : ℝ)|^4863 ≤ (22255291543481/50000000000000 : ℝ)^3839
        have hw : |(2639102367/5000000000 : ℝ)|=(2639102367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1512862511/10000000000 : ℝ)|^4863 ≤ (9141602732967/100000000000000 : ℝ)^3839
        have hw : |(-1512862511/10000000000 : ℝ)|=(1512862511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362364611/2500000000 : ℝ)|^4863 ≤ (2896738385103/6250000000000 : ℝ)^3839
        have hw : |(1362364611/2500000000 : ℝ)|=(1362364611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s6_6 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2095894281/5000000000 : ℝ)*x 0 + (1134464107/2500000000 : ℝ)*x 1 + (966497189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095894281/5000000000 : ℝ)^4863 ≤ (3324142534133/10000000000000 : ℝ)^3839 := by
    have hnat : (2095894281 : ℕ)^4863*10000000000000^3839 ≤ 3324142534133^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095894281 5000000000 3324142534133 10000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134464107/2500000000 : ℝ)^4863 ≤ (18377670186489/50000000000000 : ℝ)^3839 := by
    have hnat : (1134464107 : ℕ)^4863*50000000000000^3839 ≤ 18377670186489^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134464107 2500000000 18377670186489 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966497189/2500000000 : ℝ)^4863 ≤ (30003234271327/100000000000000 : ℝ)^3839 := by
    have hnat : (966497189 : ℕ)^4863*100000000000000^3839 ≤ 30003234271327^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966497189 2500000000 30003234271327 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095894281/5000000000 : ℝ), (1134464107/2500000000 : ℝ), (966497189/2500000000 : ℝ)] ![(3324142534133/10000000000000 : ℝ), (18377670186489/50000000000000 : ℝ), (30003234271327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095894281/5000000000 : ℝ)|^4863 ≤ (3324142534133/10000000000000 : ℝ)^3839
        have hw : |(2095894281/5000000000 : ℝ)|=(2095894281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134464107/2500000000 : ℝ)|^4863 ≤ (18377670186489/50000000000000 : ℝ)^3839
        have hw : |(1134464107/2500000000 : ℝ)|=(1134464107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(966497189/2500000000 : ℝ)|^4863 ≤ (30003234271327/100000000000000 : ℝ)^3839
        have hw : |(966497189/2500000000 : ℝ)|=(966497189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1636_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8147/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2119/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8147/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8147/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5297/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8147/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5297/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8147/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5297/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8147/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5297/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8147/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5297/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8147/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5297/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5297/50000 : ℝ) ^ (4859/1024 : ℝ) ≤ (47296096216537/2000000000000000000 : ℝ) := by
    have hpowers : (5297/50000 : ℝ)^4859 ≤ (47296096216537/2000000000000000000 : ℝ)^1024 := by
      have hnat : (5297 : ℕ)^4859*2000000000000000000^1024 ≤ 47296096216537^1024*50000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5297 50000 47296096216537 2000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5297/50000 : ℝ)) (X := (47296096216537/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8147/50000 : ℝ) ^ (4859/1024 : ℝ) ≤ (3647616306053787/20000000000000000000 : ℝ) := by
    have hpowers : (8147/50000 : ℝ)^4859 ≤ (3647616306053787/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8147 : ℕ)^4859*20000000000000000000^1024 ≤ 3647616306053787^1024*50000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8147 50000 3647616306053787 20000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8147/50000 : ℝ)) (X := (3647616306053787/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000047296096216537/1000000000000000000 : ℝ) ≤ (2000019934265739/2000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (1000047296096216537/1000000000000000000 : ℝ)^1024 ≤ (2000019934265739/2000000000000000 : ℝ)^4859 := by
      have hnat : (1000047296096216537 : ℕ)^1024*2000000000000000^4859 ≤ 2000019934265739^4859*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000047296096216537 1000000000000000000 2000019934265739 2000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000019934265739/2000000000000000 : ℝ)) (X := (1000047296096216537/1000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004120577268219157/20000000000000000000 : ℝ) ≤ (5000217078004799/5000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (20004120577268219157/20000000000000000000 : ℝ)^1024 ≤ (5000217078004799/5000000000000000 : ℝ)^4859 := by
      have hnat : (20004120577268219157 : ℕ)^1024*5000000000000000^4859 ≤ 5000217078004799^4859*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004120577268219157 20000000000000000000 5000217078004799 5000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000217078004799/5000000000000000 : ℝ)) (X := (20004120577268219157/20000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003647616306053787/10000000000000000000 : ℝ) ≤ (10000768640690501/10000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (10003647616306053787/10000000000000000000 : ℝ)^1024 ≤ (10000768640690501/10000000000000000 : ℝ)^4859 := by
      have hnat : (10003647616306053787 : ℕ)^1024*10000000000000000^4859 ≤ 10000768640690501^4859*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003647616306053787 10000000000000000000 10000768640690501 10000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000768640690501/10000000000000000 : ℝ)) (X := (10003647616306053787/10000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(47296096216537/2000000000000000000 : ℝ) ≤ ((890523141643040449/890625000000000000 : ℝ)+2*(334484680903/570000000000000 : ℝ)*(5297/50000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (890523141643040449/890625000000000000 : ℝ)+2*(334484680903/570000000000000 : ℝ)*(5297/50000 : ℝ)=(2000019934265739/2000000000000000 : ℝ) by norm_num, show 1+2*(47296096216537/2000000000000000000 : ℝ)=(1000047296096216537/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3647616306053787/20000000000000000000 : ℝ)+(47296096216537/2000000000000000000 : ℝ) ≤ ((890523141643040449/890625000000000000 : ℝ)+(334484680903/570000000000000 : ℝ)*((8147/50000 : ℝ)+(5297/50000 : ℝ)))^(4859/1024 : ℝ) := by
    rw [show (890523141643040449/890625000000000000 : ℝ)+(334484680903/570000000000000 : ℝ)*((8147/50000 : ℝ)+(5297/50000 : ℝ))=(5000217078004799/5000000000000000 : ℝ) by norm_num, show 1+(3647616306053787/20000000000000000000 : ℝ)+(47296096216537/2000000000000000000 : ℝ)=(20004120577268219157/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3647616306053787/20000000000000000000 : ℝ) ≤ ((890523141643040449/890625000000000000 : ℝ)+2*(334484680903/570000000000000 : ℝ)*(8147/50000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (890523141643040449/890625000000000000 : ℝ)+2*(334484680903/570000000000000 : ℝ)*(8147/50000 : ℝ)=(10000768640690501/10000000000000000 : ℝ) by norm_num, show 1+2*(3647616306053787/20000000000000000000 : ℝ)=(10003647616306053787/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (890523141643040449/890625000000000000 : ℝ)*(X 1 0+X 2 0)+(334484680903/570000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (8147/50000 : ℝ)) (c := (890523141643040449/890625000000000000 : ℝ)) (alpha := (334484680903/570000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (890523141643040449/890625000000000000 : ℝ)*(X 0 1+X 2 1)+(334484680903/570000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (8147/50000 : ℝ)) (c := (890523141643040449/890625000000000000 : ℝ)) (alpha := (334484680903/570000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (890523141643040449/890625000000000000 : ℝ)*(X 0 2+X 1 2)+(334484680903/570000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (8147/50000 : ℝ)) (c := (890523141643040449/890625000000000000 : ℝ)) (alpha := (334484680903/570000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-102561231/625000000 : ℝ)*X 0 0+(5451496673/10000000000 : ℝ)*X 0 1+(5183101053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53497783/100000000 : ℝ)*X 1 0+(-1779218391/10000000000 : ℝ)*X 1 1+(5183102481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674889371/5000000000 : ℝ)*X 2 0+(5183102293/10000000000 : ℝ)*X 2 1+(-889609023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((838324193/2000000000 : ℝ)*X 0 0+(772161687/2000000000 : ℝ)*X 0 1+(454298243/1000000000 : ℝ)*X 0 2+(838324193/2000000000 : ℝ)*X 1 0+(772161687/2000000000 : ℝ)*X 1 1+(454298243/1000000000 : ℝ)*X 1 2+(838324193/2000000000 : ℝ)*X 2 0+(772161687/2000000000 : ℝ)*X 2 1+(454298243/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-820522941/5000000000 : ℝ)*X 0 0+(1296279527/2500000000 : ℝ)*X 0 1+(2724729173/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639102367/5000000000 : ℝ)*X 1 0+(-1512862511/10000000000 : ℝ)*X 1 1+(1362364611/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2095894281/5000000000 : ℝ)*X 0 0+(1134464107/2500000000 : ℝ)*X 0 1+(966497189/2500000000 : ℝ)*X 0 2+(2095894281/5000000000 : ℝ)*X 1 0+(1134464107/2500000000 : ℝ)*X 1 1+(966497189/2500000000 : ℝ)*X 1 2+(2095894281/5000000000 : ℝ)*X 2 0+(1134464107/2500000000 : ℝ)*X 2 1+(966497189/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (928534224530652058605293/1855468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (603337273/100000000000000 : ℝ)*(base19) + (226922771/25000000000000 : ℝ)*(base23) + (294083/1000000000000 : ℝ)*(lower2) + (1070501/1562500000000 : ℝ)*(upper5) + (1297958727021101/50000000000000 : ℝ)*(major0) + (1297958727021101/50000000000000 : ℝ)*(major1) + (1297958727021101/50000000000000 : ℝ)*(major2) + (1862936953290979/50000000000000 : ℝ)*(sp0) + (3725904189600913/100000000000000 : ℝ)*(sp1) + (1862953866917737/50000000000000 : ℝ)*(sp2) + (293182756257549/20000000000000 : ℝ)*(sp3) + (173674723/500000000000 : ℝ)*(sp4) + (3848588373/100000000000000 : ℝ)*(sp5) + (12468589059/100000000000000 : ℝ)*(sp6) + (366481562469201/25000000000000 : ℝ)*(f.failure) + (1862954320763279/50000000000000 : ℝ)*(f.sum) + (68481947345453/14250000000000000000000000000 : ℝ)*base65 + (32968673444705233/4687500000000000000000000000000 : ℝ)*base68 + (27049211571267733/4687500000000000000000000000000 : ℝ)*base70 + (41501188619705233/4687500000000000000000000000000 : ℝ)*base72 + (47249707325047/14250000000000000000000000000 : ℝ)*base74 + (49722664966580233/4687500000000000000000000000000 : ℝ)*base76 + (10175319991580233/4687500000000000000000000000000 : ℝ)*base78 + (15617889138455233/4687500000000000000000000000000 : ℝ)*base80 + (19641791653297/14250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9498569/2500000000000000000000 : ℝ)*base89 + (9498569/2500000000000000000000 : ℝ)*base91 + (9498569/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1636_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8147/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2119/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8147/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1636_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1636_box_0 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-688932567/5000000000 : ℝ)*x 0 + (676441257/1250000000 : ℝ)*x 1 + (676441307/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (688932567/5000000000 : ℝ)^4863 ≤ (1015107540199/12500000000000 : ℝ)^3839 := by
    have hnat : (688932567 : ℕ)^4863*12500000000000^3839 ≤ 1015107540199^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688932567 5000000000 1015107540199 12500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676441257/1250000000 : ℝ)^4863 ≤ (22969783841841/50000000000000 : ℝ)^3839 := by
    have hnat : (676441257 : ℕ)^4863*50000000000000^3839 ≤ 22969783841841^3839*1250000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676441257 1250000000 22969783841841 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676441307/1250000000 : ℝ)^4863 ≤ (45939571985113/100000000000000 : ℝ)^3839 := by
    have hnat : (676441307 : ℕ)^4863*100000000000000^3839 ≤ 45939571985113^3839*1250000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676441307 1250000000 45939571985113 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-688932567/5000000000 : ℝ), (676441257/1250000000 : ℝ), (676441307/1250000000 : ℝ)] ![(1015107540199/12500000000000 : ℝ), (22969783841841/50000000000000 : ℝ), (45939571985113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-688932567/5000000000 : ℝ)|^4863 ≤ (1015107540199/12500000000000 : ℝ)^3839
        have hw : |(-688932567/5000000000 : ℝ)|=(688932567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676441257/1250000000 : ℝ)|^4863 ≤ (22969783841841/50000000000000 : ℝ)^3839
        have hw : |(676441257/1250000000 : ℝ)|=(676441257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676441307/1250000000 : ℝ)|^4863 ≤ (45939571985113/100000000000000 : ℝ)^3839
        have hw : |(676441307/1250000000 : ℝ)|=(676441307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_1 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251225941/10000000000 : ℝ)*x 0 + (-1603114827/10000000000 : ℝ)*x 1 + (5411530249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251225941/10000000000 : ℝ)^4863 ≤ (44222585268441/100000000000000 : ℝ)^3839 := by
    have hnat : (5251225941 : ℕ)^4863*100000000000000^3839 ≤ 44222585268441^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251225941 10000000000 44222585268441 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1603114827/10000000000 : ℝ)^4863 ≤ (1229730619817/12500000000000 : ℝ)^3839 := by
    have hnat : (1603114827 : ℕ)^4863*12500000000000^3839 ≤ 1229730619817^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1603114827 10000000000 1229730619817 12500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411530249/10000000000 : ℝ)^4863 ≤ (45939569759123/100000000000000 : ℝ)^3839 := by
    have hnat : (5411530249 : ℕ)^4863*100000000000000^3839 ≤ 45939569759123^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411530249 10000000000 45939569759123 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251225941/10000000000 : ℝ), (-1603114827/10000000000 : ℝ), (5411530249/10000000000 : ℝ)] ![(44222585268441/100000000000000 : ℝ), (1229730619817/12500000000000 : ℝ), (45939569759123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251225941/10000000000 : ℝ)|^4863 ≤ (44222585268441/100000000000000 : ℝ)^3839
        have hw : |(5251225941/10000000000 : ℝ)|=(5251225941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1603114827/10000000000 : ℝ)|^4863 ≤ (1229730619817/12500000000000 : ℝ)^3839
        have hw : |(-1603114827/10000000000 : ℝ)|=(1603114827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411530249/10000000000 : ℝ)|^4863 ≤ (45939569759123/100000000000000 : ℝ)^3839
        have hw : |(5411530249/10000000000 : ℝ)|=(5411530249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_2 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328201627/625000000 : ℝ)*x 0 + (1352882559/2500000000 : ℝ)*x 1 + (-10019467/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328201627/625000000 : ℝ)^4863 ≤ (44222586239199/100000000000000 : ℝ)^3839 := by
    have hnat : (328201627 : ℕ)^4863*100000000000000^3839 ≤ 44222586239199^3839*625000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328201627 625000000 44222586239199 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352882559/2500000000 : ℝ)^4863 ≤ (22969784809663/50000000000000 : ℝ)^3839 := by
    have hnat : (1352882559 : ℕ)^4863*50000000000000^3839 ≤ 22969784809663^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352882559 2500000000 22969784809663 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10019467/62500000 : ℝ)^4863 ≤ (4918922063381/50000000000000 : ℝ)^3839 := by
    have hnat : (10019467 : ℕ)^4863*50000000000000^3839 ≤ 4918922063381^3839*62500000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10019467 62500000 4918922063381 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328201627/625000000 : ℝ), (1352882559/2500000000 : ℝ), (-10019467/62500000 : ℝ)] ![(44222586239199/100000000000000 : ℝ), (22969784809663/50000000000000 : ℝ), (4918922063381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328201627/625000000 : ℝ)|^4863 ≤ (44222586239199/100000000000000 : ℝ)^3839
        have hw : |(328201627/625000000 : ℝ)|=(328201627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352882559/2500000000 : ℝ)|^4863 ≤ (22969784809663/50000000000000 : ℝ)^3839
        have hw : |(1352882559/2500000000 : ℝ)|=(1352882559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10019467/62500000 : ℝ)|^4863 ≤ (4918922063381/50000000000000 : ℝ)^3839
        have hw : |(-10019467/62500000 : ℝ)|=(10019467/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_3 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (893878357/2000000000 : ℝ)*x 0 + (2032494329/5000000000 : ℝ)*x 1 + (2032494503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893878357/2000000000 : ℝ)^4863 ≤ (36054298123343/100000000000000 : ℝ)^3839 := by
    have hnat : (893878357 : ℕ)^4863*100000000000000^3839 ≤ 36054298123343^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893878357 2000000000 36054298123343 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2032494329/5000000000 : ℝ)^4863 ≤ (15986424598823/50000000000000 : ℝ)^3839 := by
    have hnat : (2032494329 : ℕ)^4863*50000000000000^3839 ≤ 15986424598823^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032494329 5000000000 15986424598823 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2032494503/5000000000 : ℝ)^4863 ≤ (15986426332457/50000000000000 : ℝ)^3839 := by
    have hnat : (2032494503 : ℕ)^4863*50000000000000^3839 ≤ 15986426332457^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032494503 5000000000 15986426332457 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(893878357/2000000000 : ℝ), (2032494329/5000000000 : ℝ), (2032494503/5000000000 : ℝ)] ![(36054298123343/100000000000000 : ℝ), (15986424598823/50000000000000 : ℝ), (15986426332457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(893878357/2000000000 : ℝ)|^4863 ≤ (36054298123343/100000000000000 : ℝ)^3839
        have hw : |(893878357/2000000000 : ℝ)|=(893878357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2032494329/5000000000 : ℝ)|^4863 ≤ (15986424598823/50000000000000 : ℝ)^3839
        have hw : |(2032494329/5000000000 : ℝ)|=(2032494329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2032494503/5000000000 : ℝ)|^4863 ≤ (15986426332457/50000000000000 : ℝ)^3839
        have hw : |(2032494503/5000000000 : ℝ)|=(2032494503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_4 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914740421/10000000000 : ℝ)*x 0 + (2607656859/5000000000 : ℝ)*x 1 + (5215312713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914740421/10000000000 : ℝ)^4863 ≤ (1540042455581/12500000000000 : ℝ)^3839 := by
    have hnat : (1914740421 : ℕ)^4863*12500000000000^3839 ≤ 1540042455581^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914740421 10000000000 1540042455581 12500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607656859/5000000000 : ℝ)^4863 ≤ (43839835521147/100000000000000 : ℝ)^3839 := by
    have hnat : (2607656859 : ℕ)^4863*100000000000000^3839 ≤ 43839835521147^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607656859 5000000000 43839835521147 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215312713/10000000000 : ℝ)^4863 ≤ (8767964963949/20000000000000 : ℝ)^3839 := by
    have hnat : (5215312713 : ℕ)^4863*20000000000000^3839 ≤ 8767964963949^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215312713 10000000000 8767964963949 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914740421/10000000000 : ℝ), (2607656859/5000000000 : ℝ), (5215312713/10000000000 : ℝ)] ![(1540042455581/12500000000000 : ℝ), (43839835521147/100000000000000 : ℝ), (8767964963949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914740421/10000000000 : ℝ)|^4863 ≤ (1540042455581/12500000000000 : ℝ)^3839
        have hw : |(-1914740421/10000000000 : ℝ)|=(1914740421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607656859/5000000000 : ℝ)|^4863 ≤ (43839835521147/100000000000000 : ℝ)^3839
        have hw : |(2607656859/5000000000 : ℝ)|=(2607656859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215312713/10000000000 : ℝ)|^4863 ≤ (8767964963949/20000000000000 : ℝ)^3839
        have hw : |(5215312713/10000000000 : ℝ)|=(5215312713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_5 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (673270157/1250000000 : ℝ)*x 0 + (-1686849237/10000000000 : ℝ)*x 1 + (5215312957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673270157/1250000000 : ℝ)^4863 ≤ (9133386614959/20000000000000 : ℝ)^3839 := by
    have hnat : (673270157 : ℕ)^4863*20000000000000^3839 ≤ 9133386614959^3839*1250000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673270157 1250000000 9133386614959 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1686849237/10000000000 : ℝ)^4863 ≤ (10493239487023/100000000000000 : ℝ)^3839 := by
    have hnat : (1686849237 : ℕ)^4863*100000000000000^3839 ≤ 10493239487023^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686849237 10000000000 10493239487023 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215312957/10000000000 : ℝ)^4863 ≤ (43839827417897/100000000000000 : ℝ)^3839 := by
    have hnat : (5215312957 : ℕ)^4863*100000000000000^3839 ≤ 43839827417897^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215312957 10000000000 43839827417897 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673270157/1250000000 : ℝ), (-1686849237/10000000000 : ℝ), (5215312957/10000000000 : ℝ)] ![(9133386614959/20000000000000 : ℝ), (10493239487023/100000000000000 : ℝ), (43839827417897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673270157/1250000000 : ℝ)|^4863 ≤ (9133386614959/20000000000000 : ℝ)^3839
        have hw : |(673270157/1250000000 : ℝ)|=(673270157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1686849237/10000000000 : ℝ)|^4863 ≤ (10493239487023/100000000000000 : ℝ)^3839
        have hw : |(-1686849237/10000000000 : ℝ)|=(1686849237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215312957/10000000000 : ℝ)|^4863 ≤ (43839827417897/100000000000000 : ℝ)^3839
        have hw : |(5215312957/10000000000 : ℝ)|=(5215312957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_6 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386161303/10000000000 : ℝ)*x 0 + (651914083/1250000000 : ℝ)*x 1 + (-1686849569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386161303/10000000000 : ℝ)^4863 ≤ (2283346678979/5000000000000 : ℝ)^3839 := by
    have hnat : (5386161303 : ℕ)^4863*5000000000000^3839 ≤ 2283346678979^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386161303 10000000000 2283346678979 5000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651914083/1250000000 : ℝ)^4863 ≤ (8767964859597/20000000000000 : ℝ)^3839 := by
    have hnat : (651914083 : ℕ)^4863*20000000000000^3839 ≤ 8767964859597^3839*1250000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651914083 1250000000 8767964859597 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1686849569/10000000000 : ℝ)^4863 ≤ (5246621051571/50000000000000 : ℝ)^3839 := by
    have hnat : (1686849569 : ℕ)^4863*50000000000000^3839 ≤ 5246621051571^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686849569 10000000000 5246621051571 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386161303/10000000000 : ℝ), (651914083/1250000000 : ℝ), (-1686849569/10000000000 : ℝ)] ![(2283346678979/5000000000000 : ℝ), (8767964859597/20000000000000 : ℝ), (5246621051571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386161303/10000000000 : ℝ)|^4863 ≤ (2283346678979/5000000000000 : ℝ)^3839
        have hw : |(5386161303/10000000000 : ℝ)|=(5386161303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651914083/1250000000 : ℝ)|^4863 ≤ (8767964859597/20000000000000 : ℝ)^3839
        have hw : |(651914083/1250000000 : ℝ)|=(651914083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1686849569/10000000000 : ℝ)|^4863 ≤ (5246621051571/50000000000000 : ℝ)^3839
        have hw : |(-1686849569/10000000000 : ℝ)|=(1686849569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_7 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (390755339/1000000000 : ℝ)*x 0 + (4345577011/10000000000 : ℝ)*x 1 + (4345577081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390755339/1000000000 : ℝ)^4863 ≤ (30412436755599/100000000000000 : ℝ)^3839 := by
    have hnat : (390755339 : ℕ)^4863*100000000000000^3839 ≤ 30412436755599^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390755339 1000000000 30412436755599 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4345577011/10000000000 : ℝ)^4863 ≤ (4349222657381/12500000000000 : ℝ)^3839 := by
    have hnat : (4345577011 : ℕ)^4863*12500000000000^3839 ≤ 4349222657381^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345577011 10000000000 4349222657381 12500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4345577081/10000000000 : ℝ)^4863 ≤ (6958756393803/20000000000000 : ℝ)^3839 := by
    have hnat : (4345577081 : ℕ)^4863*20000000000000^3839 ≤ 6958756393803^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345577081 10000000000 6958756393803 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(390755339/1000000000 : ℝ), (4345577011/10000000000 : ℝ), (4345577081/10000000000 : ℝ)] ![(30412436755599/100000000000000 : ℝ), (4349222657381/12500000000000 : ℝ), (6958756393803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(390755339/1000000000 : ℝ)|^4863 ≤ (30412436755599/100000000000000 : ℝ)^3839
        have hw : |(390755339/1000000000 : ℝ)|=(390755339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4345577011/10000000000 : ℝ)|^4863 ≤ (4349222657381/12500000000000 : ℝ)^3839
        have hw : |(4345577011/10000000000 : ℝ)|=(4345577011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4345577081/10000000000 : ℝ)|^4863 ≤ (6958756393803/20000000000000 : ℝ)^3839
        have hw : |(4345577081/10000000000 : ℝ)|=(4345577081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_8 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1800338711/10000000000 : ℝ)*x 0 + (2537264277/5000000000 : ℝ)*x 1 + (2720579437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1800338711/10000000000 : ℝ)^4863 ≤ (1823266991/16000000000 : ℝ)^3839 := by
    have hnat : (1800338711 : ℕ)^4863*16000000000^3839 ≤ 1823266991^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800338711 10000000000 1823266991 16000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2537264277/5000000000 : ℝ)^4863 ≤ (21173082730679/50000000000000 : ℝ)^3839 := by
    have hnat : (2537264277 : ℕ)^4863*50000000000000^3839 ≤ 21173082730679^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537264277 5000000000 21173082730679 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720579437/5000000000 : ℝ)^4863 ≤ (23129207915887/50000000000000 : ℝ)^3839 := by
    have hnat : (2720579437 : ℕ)^4863*50000000000000^3839 ≤ 23129207915887^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720579437 5000000000 23129207915887 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1800338711/10000000000 : ℝ), (2537264277/5000000000 : ℝ), (2720579437/5000000000 : ℝ)] ![(1823266991/16000000000 : ℝ), (21173082730679/50000000000000 : ℝ), (23129207915887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1800338711/10000000000 : ℝ)|^4863 ≤ (1823266991/16000000000 : ℝ)^3839
        have hw : |(-1800338711/10000000000 : ℝ)|=(1800338711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2537264277/5000000000 : ℝ)|^4863 ≤ (21173082730679/50000000000000 : ℝ)^3839
        have hw : |(2537264277/5000000000 : ℝ)|=(2537264277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720579437/5000000000 : ℝ)|^4863 ≤ (23129207915887/50000000000000 : ℝ)^3839
        have hw : |(2720579437/5000000000 : ℝ)|=(2720579437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_9 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046170241/2000000000 : ℝ)*x 0 + (-1590030693/10000000000 : ℝ)*x 1 + (1088231627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046170241/2000000000 : ℝ)^4863 ≤ (44005346883291/100000000000000 : ℝ)^3839 := by
    have hnat : (1046170241 : ℕ)^4863*100000000000000^3839 ≤ 44005346883291^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046170241 2000000000 44005346883291 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1590030693/10000000000 : ℝ)^4863 ≤ (9736245230547/100000000000000 : ℝ)^3839 := by
    have hnat : (1590030693 : ℕ)^4863*100000000000000^3839 ≤ 9736245230547^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590030693 10000000000 9736245230547 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088231627/2000000000 : ℝ)^4863 ≤ (23129203936649/50000000000000 : ℝ)^3839 := by
    have hnat : (1088231627 : ℕ)^4863*50000000000000^3839 ≤ 23129203936649^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088231627 2000000000 23129203936649 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046170241/2000000000 : ℝ), (-1590030693/10000000000 : ℝ), (1088231627/2000000000 : ℝ)] ![(44005346883291/100000000000000 : ℝ), (9736245230547/100000000000000 : ℝ), (23129203936649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046170241/2000000000 : ℝ)|^4863 ≤ (44005346883291/100000000000000 : ℝ)^3839
        have hw : |(1046170241/2000000000 : ℝ)|=(1046170241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1590030693/10000000000 : ℝ)|^4863 ≤ (9736245230547/100000000000000 : ℝ)^3839
        have hw : |(-1590030693/10000000000 : ℝ)|=(1590030693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088231627/2000000000 : ℝ)|^4863 ≤ (23129203936649/50000000000000 : ℝ)^3839
        have hw : |(1088231627/2000000000 : ℝ)|=(1088231627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_10 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046169963/2000000000 : ℝ)*x 0 + (544115911/1000000000 : ℝ)*x 1 + (-1590031249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046169963/2000000000 : ℝ)^4863 ≤ (22002666035299/50000000000000 : ℝ)^3839 := by
    have hnat : (1046169963 : ℕ)^4863*50000000000000^3839 ≤ 22002666035299^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046169963 2000000000 22002666035299 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544115911/1000000000 : ℝ)^4863 ≤ (23129209186659/50000000000000 : ℝ)^3839 := by
    have hnat : (544115911 : ℕ)^4863*50000000000000^3839 ≤ 23129209186659^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544115911 1000000000 23129209186659 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1590031249/10000000000 : ℝ)^4863 ≤ (1217031192903/12500000000000 : ℝ)^3839 := by
    have hnat : (1590031249 : ℕ)^4863*12500000000000^3839 ≤ 1217031192903^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590031249 10000000000 1217031192903 12500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046169963/2000000000 : ℝ), (544115911/1000000000 : ℝ), (-1590031249/10000000000 : ℝ)] ![(22002666035299/50000000000000 : ℝ), (23129209186659/50000000000000 : ℝ), (1217031192903/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046169963/2000000000 : ℝ)|^4863 ≤ (22002666035299/50000000000000 : ℝ)^3839
        have hw : |(1046169963/2000000000 : ℝ)|=(1046169963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544115911/1000000000 : ℝ)|^4863 ≤ (23129209186659/50000000000000 : ℝ)^3839
        have hw : |(544115911/1000000000 : ℝ)|=(544115911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1590031249/10000000000 : ℝ)|^4863 ≤ (1217031192903/12500000000000 : ℝ)^3839
        have hw : |(-1590031249/10000000000 : ℝ)|=(1590031249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_11 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4551842989/10000000000 : ℝ)*x 0 + (125704507/312500000 : ℝ)*x 1 + (4022544167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4551842989/10000000000 : ℝ)^4863 ≤ (4612363030161/12500000000000 : ℝ)^3839 := by
    have hnat : (4551842989 : ℕ)^4863*12500000000000^3839 ≤ 4612363030161^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551842989 10000000000 4612363030161 12500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125704507/312500000 : ℝ)^4863 ≤ (15775274078891/50000000000000 : ℝ)^3839 := by
    have hnat : (125704507 : ℕ)^4863*50000000000000^3839 ≤ 15775274078891^3839*312500000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125704507 312500000 15775274078891 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022544167/10000000000 : ℝ)^4863 ≤ (6310109518291/20000000000000 : ℝ)^3839 := by
    have hnat : (4022544167 : ℕ)^4863*20000000000000^3839 ≤ 6310109518291^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022544167 10000000000 6310109518291 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4551842989/10000000000 : ℝ), (125704507/312500000 : ℝ), (4022544167/10000000000 : ℝ)] ![(4612363030161/12500000000000 : ℝ), (15775274078891/50000000000000 : ℝ), (6310109518291/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4551842989/10000000000 : ℝ)|^4863 ≤ (4612363030161/12500000000000 : ℝ)^3839
        have hw : |(4551842989/10000000000 : ℝ)|=(4551842989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125704507/312500000 : ℝ)|^4863 ≤ (15775274078891/50000000000000 : ℝ)^3839
        have hw : |(125704507/312500000 : ℝ)|=(125704507/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022544167/10000000000 : ℝ)|^4863 ≤ (6310109518291/20000000000000 : ℝ)^3839
        have hw : |(4022544167/10000000000 : ℝ)|=(4022544167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_12 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1490678791/10000000000 : ℝ)*x 0 + (2773410593/5000000000 : ℝ)*x 1 + (2597733567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1490678791/10000000000 : ℝ)^4863 ≤ (8972133760977/100000000000000 : ℝ)^3839 := by
    have hnat : (1490678791 : ℕ)^4863*100000000000000^3839 ≤ 8972133760977^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490678791 10000000000 8972133760977 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2773410593/5000000000 : ℝ)^4863 ≤ (47399252979203/100000000000000 : ℝ)^3839 := by
    have hnat : (2773410593 : ℕ)^4863*100000000000000^3839 ≤ 47399252979203^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2773410593 5000000000 47399252979203 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597733567/5000000000 : ℝ)^4863 ≤ (21814306620671/50000000000000 : ℝ)^3839 := by
    have hnat : (2597733567 : ℕ)^4863*50000000000000^3839 ≤ 21814306620671^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597733567 5000000000 21814306620671 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1490678791/10000000000 : ℝ), (2773410593/5000000000 : ℝ), (2597733567/5000000000 : ℝ)] ![(8972133760977/100000000000000 : ℝ), (47399252979203/100000000000000 : ℝ), (21814306620671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1490678791/10000000000 : ℝ)|^4863 ≤ (8972133760977/100000000000000 : ℝ)^3839
        have hw : |(-1490678791/10000000000 : ℝ)|=(1490678791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2773410593/5000000000 : ℝ)|^4863 ≤ (47399252979203/100000000000000 : ℝ)^3839
        have hw : |(2773410593/5000000000 : ℝ)|=(2773410593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597733567/5000000000 : ℝ)|^4863 ≤ (21814306620671/50000000000000 : ℝ)^3839
        have hw : |(2597733567/5000000000 : ℝ)|=(2597733567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_13 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5399817171/10000000000 : ℝ)*x 0 + (-847514377/5000000000 : ℝ)*x 1 + (5195467453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399817171/10000000000 : ℝ)^4863 ≤ (45813648640423/100000000000000 : ℝ)^3839 := by
    have hnat : (5399817171 : ℕ)^4863*100000000000000^3839 ≤ 45813648640423^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399817171 10000000000 45813648640423 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847514377/5000000000 : ℝ)^4863 ≤ (5278867356473/50000000000000 : ℝ)^3839 := by
    have hnat : (847514377 : ℕ)^4863*50000000000000^3839 ≤ 5278867356473^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847514377 5000000000 5278867356473 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195467453/10000000000 : ℝ)^4863 ≤ (43628616634653/100000000000000 : ℝ)^3839 := by
    have hnat : (5195467453 : ℕ)^4863*100000000000000^3839 ≤ 43628616634653^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195467453 10000000000 43628616634653 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399817171/10000000000 : ℝ), (-847514377/5000000000 : ℝ), (5195467453/10000000000 : ℝ)] ![(45813648640423/100000000000000 : ℝ), (5278867356473/50000000000000 : ℝ), (43628616634653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399817171/10000000000 : ℝ)|^4863 ≤ (45813648640423/100000000000000 : ℝ)^3839
        have hw : |(5399817171/10000000000 : ℝ)|=(5399817171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-847514377/5000000000 : ℝ)|^4863 ≤ (5278867356473/50000000000000 : ℝ)^3839
        have hw : |(-847514377/5000000000 : ℝ)|=(847514377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195467453/10000000000 : ℝ)|^4863 ≤ (43628616634653/100000000000000 : ℝ)^3839
        have hw : |(5195467453/10000000000 : ℝ)|=(5195467453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_14 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1349954367/2500000000 : ℝ)*x 0 + (5195466999/10000000000 : ℝ)*x 1 + (-847514481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349954367/2500000000 : ℝ)^4863 ≤ (45813651832391/100000000000000 : ℝ)^3839 := by
    have hnat : (1349954367 : ℕ)^4863*100000000000000^3839 ≤ 45813651832391^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349954367 2500000000 45813651832391 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195466999/10000000000 : ℝ)^4863 ≤ (21814305902651/50000000000000 : ℝ)^3839 := by
    have hnat : (5195466999 : ℕ)^4863*50000000000000^3839 ≤ 21814305902651^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195466999 10000000000 21814305902651 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847514481/5000000000 : ℝ)^4863 ≤ (2639434088519/25000000000000 : ℝ)^3839 := by
    have hnat : (847514481 : ℕ)^4863*25000000000000^3839 ≤ 2639434088519^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847514481 5000000000 2639434088519 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349954367/2500000000 : ℝ), (5195466999/10000000000 : ℝ), (-847514481/5000000000 : ℝ)] ![(45813651832391/100000000000000 : ℝ), (21814305902651/50000000000000 : ℝ), (2639434088519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349954367/2500000000 : ℝ)|^4863 ≤ (45813651832391/100000000000000 : ℝ)^3839
        have hw : |(1349954367/2500000000 : ℝ)|=(1349954367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195466999/10000000000 : ℝ)|^4863 ≤ (21814305902651/50000000000000 : ℝ)^3839
        have hw : |(5195466999/10000000000 : ℝ)|=(5195466999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-847514481/5000000000 : ℝ)|^4863 ≤ (2639434088519/25000000000000 : ℝ)^3839
        have hw : |(-847514481/5000000000 : ℝ)|=(847514481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_box_15 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (384910001/1000000000 : ℝ)*x 0 + (874781147/2000000000 : ℝ)*x 1 + (4373905467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (384910001/1000000000 : ℝ)^4863 ≤ (29837299396169/100000000000000 : ℝ)^3839 := by
    have hnat : (384910001 : ℕ)^4863*100000000000000^3839 ≤ 29837299396169^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384910001 1000000000 29837299396169 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874781147/2000000000 : ℝ)^4863 ≤ (17540675826079/50000000000000 : ℝ)^3839 := by
    have hnat : (874781147 : ℕ)^4863*50000000000000^3839 ≤ 17540675826079^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874781147 2000000000 17540675826079 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4373905467/10000000000 : ℝ)^4863 ≤ (35081348929283/100000000000000 : ℝ)^3839 := by
    have hnat : (4373905467 : ℕ)^4863*100000000000000^3839 ≤ 35081348929283^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373905467 10000000000 35081348929283 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(384910001/1000000000 : ℝ), (874781147/2000000000 : ℝ), (4373905467/10000000000 : ℝ)] ![(29837299396169/100000000000000 : ℝ), (17540675826079/50000000000000 : ℝ), (35081348929283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(384910001/1000000000 : ℝ)|^4863 ≤ (29837299396169/100000000000000 : ℝ)^3839
        have hw : |(384910001/1000000000 : ℝ)|=(384910001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(874781147/2000000000 : ℝ)|^4863 ≤ (17540675826079/50000000000000 : ℝ)^3839
        have hw : |(874781147/2000000000 : ℝ)|=(874781147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4373905467/10000000000 : ℝ)|^4863 ≤ (35081348929283/100000000000000 : ℝ)^3839
        have hw : |(4373905467/10000000000 : ℝ)|=(4373905467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1636_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8147/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2119/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65011/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2339/4000 : ℝ) ∧ (40469/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (44043/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8147/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2119/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8147/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2119/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8147/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2119/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8147/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2119/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8147/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2119/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8147/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2119/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2119/20000 : ℝ) ^ (4859/1024 : ℝ) ≤ (47317284171149/2000000000000000000 : ℝ) := by
    have hpowers : (2119/20000 : ℝ)^4859 ≤ (47317284171149/2000000000000000000 : ℝ)^1024 := by
      have hnat : (2119 : ℕ)^4859*2000000000000000000^1024 ≤ 47317284171149^1024*20000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2119 20000 47317284171149 2000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2119/20000 : ℝ)) (X := (47317284171149/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8147/50000 : ℝ) ^ (4859/1024 : ℝ) ≤ (3647616306053787/20000000000000000000 : ℝ) := by
    have hpowers : (8147/50000 : ℝ)^4859 ≤ (3647616306053787/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8147 : ℕ)^4859*20000000000000000000^1024 ≤ 3647616306053787^1024*50000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8147 50000 3647616306053787 20000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8147/50000 : ℝ)) (X := (3647616306053787/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000047317284171149/1000000000000000000 : ℝ) ≤ (2500024928994787/2500000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (1000047317284171149/1000000000000000000 : ℝ)^1024 ≤ (2500024928994787/2500000000000000 : ℝ)^4859 := by
      have hnat : (1000047317284171149 : ℕ)^1024*2500000000000000^4859 ≤ 2500024928994787^4859*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000047317284171149 1000000000000000000 2500024928994787 2500000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500024928994787/2500000000000000 : ℝ)) (X := (1000047317284171149/1000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004120789147765277/20000000000000000000 : ℝ) ≤ (10000434178332029/10000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (20004120789147765277/20000000000000000000 : ℝ)^1024 ≤ (10000434178332029/10000000000000000 : ℝ)^4859 := by
      have hnat : (20004120789147765277 : ℕ)^1024*10000000000000000^4859 ≤ 10000434178332029^4859*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004120789147765277 20000000000000000000 10000434178332029 10000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000434178332029/10000000000000000 : ℝ)) (X := (20004120789147765277/20000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003647616306053787/10000000000000000000 : ℝ) ≤ (1000076864068491/1000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (10003647616306053787/10000000000000000000 : ℝ)^1024 ≤ (1000076864068491/1000000000000000 : ℝ)^4859 := by
      have hnat : (10003647616306053787 : ℕ)^1024*1000000000000000^4859 ≤ 1000076864068491^4859*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003647616306053787 10000000000000000000 1000076864068491 1000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000076864068491/1000000000000000 : ℝ)) (X := (10003647616306053787/10000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(47317284171149/2000000000000000000 : ℝ) ≤ ((28491740512053808031/28495000000000000000 : ℝ)+2*(334462352881/569900000000000 : ℝ)*(2119/20000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (28491740512053808031/28495000000000000000 : ℝ)+2*(334462352881/569900000000000 : ℝ)*(2119/20000 : ℝ)=(2500024928994787/2500000000000000 : ℝ) by norm_num, show 1+2*(47317284171149/2000000000000000000 : ℝ)=(1000047317284171149/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3647616306053787/20000000000000000000 : ℝ)+(47317284171149/2000000000000000000 : ℝ) ≤ ((28491740512053808031/28495000000000000000 : ℝ)+(334462352881/569900000000000 : ℝ)*((8147/50000 : ℝ)+(2119/20000 : ℝ)))^(4859/1024 : ℝ) := by
    rw [show (28491740512053808031/28495000000000000000 : ℝ)+(334462352881/569900000000000 : ℝ)*((8147/50000 : ℝ)+(2119/20000 : ℝ))=(10000434178332029/10000000000000000 : ℝ) by norm_num, show 1+(3647616306053787/20000000000000000000 : ℝ)+(47317284171149/2000000000000000000 : ℝ)=(20004120789147765277/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3647616306053787/20000000000000000000 : ℝ) ≤ ((28491740512053808031/28495000000000000000 : ℝ)+2*(334462352881/569900000000000 : ℝ)*(8147/50000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (28491740512053808031/28495000000000000000 : ℝ)+2*(334462352881/569900000000000 : ℝ)*(8147/50000 : ℝ)=(1000076864068491/1000000000000000 : ℝ) by norm_num, show 1+2*(3647616306053787/20000000000000000000 : ℝ)=(10003647616306053787/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28491740512053808031/28495000000000000000 : ℝ)*(X 1 0+X 2 0)+(334462352881/569900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (2119/20000 : ℝ)) (hi := (8147/50000 : ℝ)) (c := (28491740512053808031/28495000000000000000 : ℝ)) (alpha := (334462352881/569900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28491740512053808031/28495000000000000000 : ℝ)*(X 0 1+X 2 1)+(334462352881/569900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (2119/20000 : ℝ)) (hi := (8147/50000 : ℝ)) (c := (28491740512053808031/28495000000000000000 : ℝ)) (alpha := (334462352881/569900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28491740512053808031/28495000000000000000 : ℝ)*(X 0 2+X 1 2)+(334462352881/569900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (2119/20000 : ℝ)) (hi := (8147/50000 : ℝ)) (c := (28491740512053808031/28495000000000000000 : ℝ)) (alpha := (334462352881/569900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-688932567/5000000000 : ℝ)*X 0 0+(676441257/1250000000 : ℝ)*X 0 1+(676441307/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251225941/10000000000 : ℝ)*X 1 0+(-1603114827/10000000000 : ℝ)*X 1 1+(5411530249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((328201627/625000000 : ℝ)*X 2 0+(1352882559/2500000000 : ℝ)*X 2 1+(-10019467/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((893878357/2000000000 : ℝ)*X 0 0+(2032494329/5000000000 : ℝ)*X 0 1+(2032494503/5000000000 : ℝ)*X 0 2+(893878357/2000000000 : ℝ)*X 1 0+(2032494329/5000000000 : ℝ)*X 1 1+(2032494503/5000000000 : ℝ)*X 1 2+(893878357/2000000000 : ℝ)*X 2 0+(2032494329/5000000000 : ℝ)*X 2 1+(2032494503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1914740421/10000000000 : ℝ)*X 0 0+(2607656859/5000000000 : ℝ)*X 0 1+(5215312713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((673270157/1250000000 : ℝ)*X 1 0+(-1686849237/10000000000 : ℝ)*X 1 1+(5215312957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5386161303/10000000000 : ℝ)*X 2 0+(651914083/1250000000 : ℝ)*X 2 1+(-1686849569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((390755339/1000000000 : ℝ)*X 0 0+(4345577011/10000000000 : ℝ)*X 0 1+(4345577081/10000000000 : ℝ)*X 0 2+(390755339/1000000000 : ℝ)*X 1 0+(4345577011/10000000000 : ℝ)*X 1 1+(4345577081/10000000000 : ℝ)*X 1 2+(390755339/1000000000 : ℝ)*X 2 0+(4345577011/10000000000 : ℝ)*X 2 1+(4345577081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1800338711/10000000000 : ℝ)*X 0 0+(2537264277/5000000000 : ℝ)*X 0 1+(2720579437/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1046170241/2000000000 : ℝ)*X 1 0+(-1590030693/10000000000 : ℝ)*X 1 1+(1088231627/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1046169963/2000000000 : ℝ)*X 2 0+(544115911/1000000000 : ℝ)*X 2 1+(-1590031249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4551842989/10000000000 : ℝ)*X 0 0+(125704507/312500000 : ℝ)*X 0 1+(4022544167/10000000000 : ℝ)*X 0 2+(4551842989/10000000000 : ℝ)*X 1 0+(125704507/312500000 : ℝ)*X 1 1+(4022544167/10000000000 : ℝ)*X 1 2+(4551842989/10000000000 : ℝ)*X 2 0+(125704507/312500000 : ℝ)*X 2 1+(4022544167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1490678791/10000000000 : ℝ)*X 0 0+(2773410593/5000000000 : ℝ)*X 0 1+(2597733567/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5399817171/10000000000 : ℝ)*X 1 0+(-847514377/5000000000 : ℝ)*X 1 1+(5195467453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1349954367/2500000000 : ℝ)*X 2 0+(5195466999/10000000000 : ℝ)*X 2 1+(-847514481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((384910001/1000000000 : ℝ)*X 0 0+(874781147/2000000000 : ℝ)*X 0 1+(4373905467/10000000000 : ℝ)*X 0 2+(384910001/1000000000 : ℝ)*X 1 0+(874781147/2000000000 : ℝ)*X 1 1+(4373905467/10000000000 : ℝ)*X 1 2+(384910001/1000000000 : ℝ)*X 2 0+(874781147/2000000000 : ℝ)*X 2 1+(4373905467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65011/100000 : ℝ) ≤ (-463105922141827763903896321058373/712375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14064023/50000000000000 : ℝ)*(lower2) + (77994893/100000000000000 : ℝ)*(lower4) + (38155319/100000000000000 : ℝ)*(lower5) + (866106576635961/50000000000000 : ℝ)*(major0) + (866106576635961/50000000000000 : ℝ)*(major1) + (866106576635961/50000000000000 : ℝ)*(major2) + (617691367/20000000000000 : ℝ)*(sp1) + (1531522473/20000000000000 : ℝ)*(sp2) + (626975484753523/25000000000000 : ℝ)*(sp4) + (626976060833617/25000000000000 : ℝ)*(sp5) + (1253949837089469/50000000000000 : ℝ)*(sp6) + (61136772518647/6250000000000 : ℝ)*(sp7) + (5392777211/100000000000000 : ℝ)*(sp8) + (190269443/100000000000000 : ℝ)*(sp15) + (195637710113559/20000000000000 : ℝ)*(f.failure) + (2507907331791303/100000000000000 : ℝ)*(f.sum) + (25305965267433/28495000000000000000000000000 : ℝ)*base66 + (6789743657520997209/1424750000000000000000000000000000 : ℝ)*base68 + (399332588923002791/1424750000000000000000000000000000 : ℝ)*base69 + (11846701814885502791/1424750000000000000000000000000000 : ℝ)*base71 + (111611388304319/14247500000000000000000000000 : ℝ)*base74 + (7028649058943252791/1424750000000000000000000000000000 : ℝ)*base75 + (3547142561951747209/1424750000000000000000000000000000 : ℝ)*base78 + (4700092846634502791/1424750000000000000000000000000000 : ℝ)*base79 + (59905874091863/28495000000000000000000000000 : ℝ)*base82 + (5723871/2000000000000000000000 : ℝ)*base89 + (5723871/2000000000000000000000 : ℝ)*base91 + (5723871/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2339/4000 : ℝ) ≤ (416578090352424376604499270496803/712375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58431513/100000000000000 : ℝ)*(lower3) + (657793/20000000000000 : ℝ)*(upper4) + (4426269/25000000000000 : ℝ)*(upper5) + (910322698356157/50000000000000 : ℝ)*(major0) + (910322698356157/50000000000000 : ℝ)*(major1) + (910322698356157/50000000000000 : ℝ)*(major2) + (2593670173884723/100000000000000 : ℝ)*(sp0) + (1296834888690381/50000000000000 : ℝ)*(sp1) + (324208910350221/12500000000000 : ℝ)*(sp2) + (102812518025791/10000000000000 : ℝ)*(sp3) + (963539819/50000000000000 : ℝ)*(sp5) + (52707329/12500000000000 : ℝ)*(sp6) + (727755451/50000000000000 : ℝ)*(sp7) + (1530575677/100000000000000 : ℝ)*(sp12) + (257031658942203/25000000000000 : ℝ)*(f.failure) + (6484179261151/250000000000 : ℝ)*(f.sum) + (32961326978161/28495000000000000000000000000 : ℝ)*base66 + (8066083775411253133/1424750000000000000000000000000000 : ℝ)*base68 + (7686974635257253133/1424750000000000000000000000000000 : ℝ)*base70 + (12148268054964253133/1424750000000000000000000000000000 : ℝ)*base72 + (3428606069689/7123750000000000000000000000 : ℝ)*base74 + (14077001035932753133/1424750000000000000000000000000000 : ℝ)*base76 + (10582025707888753133/1424750000000000000000000000000000 : ℝ)*base78 + (9387034306589753133/1424750000000000000000000000000000 : ℝ)*base80 + (14995122878149/7123750000000000000000000000 : ℝ)*base82 + (10403107/2500000000000000000000 : ℝ)*base89 + (10403107/2500000000000000000000 : ℝ)*base91 + (10403107/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40469/50000 : ℝ) ≤ (28829862033483913376979642047391/35618750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29257969/100000000000000 : ℝ)*(upper1) + (255922339/100000000000000 : ℝ)*(upper2) + (207676253/100000000000000 : ℝ)*(lower5) + (95956783674563/5000000000000 : ℝ)*(major0) + (95956783674563/5000000000000 : ℝ)*(major1) + (95956783674563/5000000000000 : ℝ)*(major2) + (3115270649/12500000000000 : ℝ)*(sp1) + (42693134559/50000000000000 : ℝ)*(sp2) + (1090852007/4000000000000 : ℝ)*(sp3) + (5449436071/50000000000000 : ℝ)*(sp4) + (1363767933838587/50000000000000 : ℝ)*(sp8) + (681880461096031/25000000000000 : ℝ)*(sp9) + (1363730690140099/50000000000000 : ℝ)*(sp10) + (1083717266287151/100000000000000 : ℝ)*(sp11) + (541872268793663/50000000000000 : ℝ)*(f.failure) + (681886691637329/25000000000000 : ℝ)*(f.sum) + (4425885588363/569900000000000000000000000 : ℝ)*base65 + (232049714691884547/142475000000000000000000000000000 : ℝ)*base68 + (900910592987190453/142475000000000000000000000000000 : ℝ)*base69 + (1282237205920115453/142475000000000000000000000000000 : ℝ)*base71 + (2581803715467/569900000000000000000000000 : ℝ)*base73 + (1921194267237840453/142475000000000000000000000000000 : ℝ)*base75 + (1776649953926465453/142475000000000000000000000000000 : ℝ)*base77 + (199266950610015453/142475000000000000000000000000000 : ℝ)*base79 + (41938292685517/5699000000000000000000000000 : ℝ)*base81 + (72644153/5000000000000000000000 : ℝ)*base90 + (72644153/5000000000000000000000 : ℝ)*base92 + (72644153/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-44043/50000 : ℝ) ≤ (-313742890234471855054754649385101/356187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5914877/50000000000000 : ℝ)*(lower2) + (76348741/100000000000000 : ℝ)*(upper3) + (30992909/100000000000000 : ℝ)*(upper5) + (490625805155157/25000000000000 : ℝ)*(major0) + (490625805155157/25000000000000 : ℝ)*(major1) + (490625805155157/25000000000000 : ℝ)*(major2) + (676220761/100000000000000 : ℝ)*(sp0) + (84523447/100000000000000 : ℝ)*(sp5) + (26660423581/50000000000000 : ℝ)*(sp6) + (5044927193/50000000000000 : ℝ)*(sp7) + (1423066294855703/50000000000000 : ℝ)*(sp12) + (35576664767609/1250000000000 : ℝ)*(sp13) + (569215989017001/20000000000000 : ℝ)*(sp14) + (1108224296449323/100000000000000 : ℝ)*(sp15) + (1108234386303709/100000000000000 : ℝ)*(f.failure) + (355766658241521/12500000000000 : ℝ)*(f.sum) + (58273932213759/14247500000000000000000000000 : ℝ)*base65 + (1489754903598890867/712375000000000000000000000000000 : ℝ)*base67 + (3186079532966890867/712375000000000000000000000000000 : ℝ)*base69 + (955069463621234133/712375000000000000000000000000000 : ℝ)*base72 + (15614890520357/7123750000000000000000000000 : ℝ)*base73 + (2663135791130734133/712375000000000000000000000000000 : ℝ)*base76 + (323259781013015867/712375000000000000000000000000000 : ℝ)*base77 + (1600194805190265867/712375000000000000000000000000000 : ℝ)*base79 + (102728830378363/28495000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (31600779/10000000000000000000000 : ℝ)*base90 + (31600779/10000000000000000000000 : ℝ)*base92 + (31600779/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1636_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8147/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2119/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65011/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2339/4000 : ℝ) else (40469/50000 : ℝ) ≤ X j i ∧ X j i ≤ (44043/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1636_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1636_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8147/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65011/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2339/4000 : ℝ) else (40469/50000 : ℝ) ≤ X j i ∧ X j i ≤ (44043/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1636_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1636_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8147/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65011/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2339/4000 : ℝ) else (40469/50000 : ℝ) ≤ X j i ∧ X j i ≤ (44043/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1636_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
