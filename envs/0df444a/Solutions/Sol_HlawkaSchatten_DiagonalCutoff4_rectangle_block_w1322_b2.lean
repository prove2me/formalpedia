-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1322_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:43:41.509916+00:00
-- url     : https://prove2.me/submissions/5a6907dd-976f-456c-b2a6-cb0ea89c32b3

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
theorem support_rectangle_w1322_s6_0 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2061369483/10000000000 : ℝ)*x 0 + (541375983/1000000000 : ℝ)*x 1 + (655494489/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061369483/10000000000 : ℝ)^2141 ≤ (6274264117491/50000000000000 : ℝ)^1629 := by
    have hnat : (2061369483 : ℕ)^2141*50000000000000^1629 ≤ 6274264117491^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061369483 10000000000 6274264117491 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541375983/1000000000 : ℝ)^2141 ≤ (8928260331163/20000000000000 : ℝ)^1629 := by
    have hnat : (541375983 : ℕ)^2141*20000000000000^1629 ≤ 8928260331163^1629*1000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541375983 1000000000 8928260331163 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655494489/1250000000 : ℝ)^2141 ≤ (21405085044381/50000000000000 : ℝ)^1629 := by
    have hnat : (655494489 : ℕ)^2141*50000000000000^1629 ≤ 21405085044381^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655494489 1250000000 21405085044381 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2061369483/10000000000 : ℝ), (541375983/1000000000 : ℝ), (655494489/1250000000 : ℝ)] ![(6274264117491/50000000000000 : ℝ), (8928260331163/20000000000000 : ℝ), (21405085044381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2061369483/10000000000 : ℝ)|^2141 ≤ (6274264117491/50000000000000 : ℝ)^1629
        have hw : |(-2061369483/10000000000 : ℝ)|=(2061369483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541375983/1000000000 : ℝ)|^2141 ≤ (8928260331163/20000000000000 : ℝ)^1629
        have hw : |(541375983/1000000000 : ℝ)|=(541375983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655494489/1250000000 : ℝ)|^2141 ≤ (21405085044381/50000000000000 : ℝ)^1629
        have hw : |(655494489/1250000000 : ℝ)|=(655494489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s6_1 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674669413/5000000000 : ℝ)*x 0 + (-536975593/2500000000 : ℝ)*x 1 + (1048791281/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674669413/5000000000 : ℝ)^2141 ≤ (8788888243413/20000000000000 : ℝ)^1629 := by
    have hnat : (2674669413 : ℕ)^2141*20000000000000^1629 ≤ 8788888243413^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674669413 5000000000 8788888243413 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (536975593/2500000000 : ℝ)^2141 ≤ (827836461733/6250000000000 : ℝ)^1629 := by
    have hnat : (536975593 : ℕ)^2141*6250000000000^1629 ≤ 827836461733^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536975593 2500000000 827836461733 6250000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048791281/2000000000 : ℝ)^2141 ≤ (21405087689227/50000000000000 : ℝ)^1629 := by
    have hnat : (1048791281 : ℕ)^2141*50000000000000^1629 ≤ 21405087689227^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048791281 2000000000 21405087689227 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674669413/5000000000 : ℝ), (-536975593/2500000000 : ℝ), (1048791281/2000000000 : ℝ)] ![(8788888243413/20000000000000 : ℝ), (827836461733/6250000000000 : ℝ), (21405087689227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674669413/5000000000 : ℝ)|^2141 ≤ (8788888243413/20000000000000 : ℝ)^1629
        have hw : |(2674669413/5000000000 : ℝ)|=(2674669413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-536975593/2500000000 : ℝ)|^2141 ≤ (827836461733/6250000000000 : ℝ)^1629
        have hw : |(-536975593/2500000000 : ℝ)|=(536975593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048791281/2000000000 : ℝ)|^2141 ≤ (21405087689227/50000000000000 : ℝ)^1629
        have hw : |(1048791281/2000000000 : ℝ)|=(1048791281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s6_2 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349339411/10000000000 : ℝ)*x 0 + (5243955561/10000000000 : ℝ)*x 1 + (-214790271/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349339411/10000000000 : ℝ)^2141 ≤ (43944447533257/100000000000000 : ℝ)^1629 := by
    have hnat : (5349339411 : ℕ)^2141*100000000000000^1629 ≤ 43944447533257^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349339411 10000000000 43944447533257 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243955561/10000000000 : ℝ)^2141 ≤ (42810166322673/100000000000000 : ℝ)^1629 := by
    have hnat : (5243955561 : ℕ)^2141*100000000000000^1629 ≤ 42810166322673^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243955561 10000000000 42810166322673 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214790271/1000000000 : ℝ)^2141 ≤ (13245386127171/100000000000000 : ℝ)^1629 := by
    have hnat : (214790271 : ℕ)^2141*100000000000000^1629 ≤ 13245386127171^1629*1000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214790271 1000000000 13245386127171 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349339411/10000000000 : ℝ), (5243955561/10000000000 : ℝ), (-214790271/1000000000 : ℝ)] ![(43944447533257/100000000000000 : ℝ), (42810166322673/100000000000000 : ℝ), (13245386127171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349339411/10000000000 : ℝ)|^2141 ≤ (43944447533257/100000000000000 : ℝ)^1629
        have hw : |(5349339411/10000000000 : ℝ)|=(5349339411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243955561/10000000000 : ℝ)|^2141 ≤ (42810166322673/100000000000000 : ℝ)^1629
        have hw : |(5243955561/10000000000 : ℝ)|=(5243955561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214790271/1000000000 : ℝ)|^2141 ≤ (13245386127171/100000000000000 : ℝ)^1629
        have hw : |(-214790271/1000000000 : ℝ)|=(214790271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s6_3 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4331873599/10000000000 : ℝ)*x 0 + (2079384489/5000000000 : ℝ)*x 1 + (56396999/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331873599/10000000000 : ℝ)^2141 ≤ (33302879806289/100000000000000 : ℝ)^1629 := by
    have hnat : (4331873599 : ℕ)^2141*100000000000000^1629 ≤ 33302879806289^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331873599 10000000000 33302879806289 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079384489/5000000000 : ℝ)^2141 ≤ (31564883539809/100000000000000 : ℝ)^1629 := by
    have hnat : (2079384489 : ℕ)^2141*100000000000000^1629 ≤ 31564883539809^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079384489 5000000000 31564883539809 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56396999/125000000 : ℝ)^2141 ≤ (8783059160759/25000000000000 : ℝ)^1629 := by
    have hnat : (56396999 : ℕ)^2141*25000000000000^1629 ≤ 8783059160759^1629*125000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56396999 125000000 8783059160759 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331873599/10000000000 : ℝ), (2079384489/5000000000 : ℝ), (56396999/125000000 : ℝ)] ![(33302879806289/100000000000000 : ℝ), (31564883539809/100000000000000 : ℝ), (8783059160759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331873599/10000000000 : ℝ)|^2141 ≤ (33302879806289/100000000000000 : ℝ)^1629
        have hw : |(4331873599/10000000000 : ℝ)|=(4331873599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079384489/5000000000 : ℝ)|^2141 ≤ (31564883539809/100000000000000 : ℝ)^1629
        have hw : |(2079384489/5000000000 : ℝ)|=(2079384489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56396999/125000000 : ℝ)|^2141 ≤ (8783059160759/25000000000000 : ℝ)^1629
        have hw : |(56396999/125000000 : ℝ)|=(56396999/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s6_4 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-32209103/156250000 : ℝ)*x 0 + (5244562847/10000000000 : ℝ)*x 1 + (1082629849/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32209103/156250000 : ℝ)^2141 ≤ (12548633117361/100000000000000 : ℝ)^1629 := by
    have hnat : (32209103 : ℕ)^2141*100000000000000^1629 ≤ 12548633117361^1629*156250000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32209103 156250000 12548633117361 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244562847/10000000000 : ℝ)^2141 ≤ (1712667295063/4000000000000 : ℝ)^1629 := by
    have hnat : (5244562847 : ℕ)^2141*4000000000000^1629 ≤ 1712667295063^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244562847 10000000000 1712667295063 4000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082629849/2000000000 : ℝ)^2141 ≤ (11158671123023/25000000000000 : ℝ)^1629 := by
    have hnat : (1082629849 : ℕ)^2141*25000000000000^1629 ≤ 11158671123023^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082629849 2000000000 11158671123023 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32209103/156250000 : ℝ), (5244562847/10000000000 : ℝ), (1082629849/2000000000 : ℝ)] ![(12548633117361/100000000000000 : ℝ), (1712667295063/4000000000000 : ℝ), (11158671123023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32209103/156250000 : ℝ)|^2141 ≤ (12548633117361/100000000000000 : ℝ)^1629
        have hw : |(-32209103/156250000 : ℝ)|=(32209103/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244562847/10000000000 : ℝ)|^2141 ≤ (1712667295063/4000000000000 : ℝ)^1629
        have hw : |(5244562847/10000000000 : ℝ)|=(5244562847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082629849/2000000000 : ℝ)|^2141 ≤ (11158671123023/25000000000000 : ℝ)^1629
        have hw : |(1082629849/2000000000 : ℝ)|=(1082629849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s6_5 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305704791/10000000000 : ℝ)*x 0 + (-1978708659/10000000000 : ℝ)*x 1 + (5413149109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305704791/10000000000 : ℝ)^2141 ≤ (2717120847943/6250000000000 : ℝ)^1629 := by
    have hnat : (5305704791 : ℕ)^2141*6250000000000^1629 ≤ 2717120847943^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305704791 10000000000 2717120847943 6250000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978708659/10000000000 : ℝ)^2141 ≤ (5945691700789/50000000000000 : ℝ)^1629 := by
    have hnat : (1978708659 : ℕ)^2141*50000000000000^1629 ≤ 5945691700789^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978708659 10000000000 5945691700789 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413149109/10000000000 : ℝ)^2141 ≤ (44634683018229/100000000000000 : ℝ)^1629 := by
    have hnat : (5413149109 : ℕ)^2141*100000000000000^1629 ≤ 44634683018229^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413149109 10000000000 44634683018229 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305704791/10000000000 : ℝ), (-1978708659/10000000000 : ℝ), (5413149109/10000000000 : ℝ)] ![(2717120847943/6250000000000 : ℝ), (5945691700789/50000000000000 : ℝ), (44634683018229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305704791/10000000000 : ℝ)|^2141 ≤ (2717120847943/6250000000000 : ℝ)^1629
        have hw : |(5305704791/10000000000 : ℝ)|=(5305704791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1978708659/10000000000 : ℝ)|^2141 ≤ (5945691700789/50000000000000 : ℝ)^1629
        have hw : |(-1978708659/10000000000 : ℝ)|=(1978708659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413149109/10000000000 : ℝ)|^2141 ≤ (44634683018229/100000000000000 : ℝ)^1629
        have hw : |(5413149109/10000000000 : ℝ)|=(5413149109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s6_6 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652852409/5000000000 : ℝ)*x 0 + (5413148901/10000000000 : ℝ)*x 1 + (-1978708907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652852409/5000000000 : ℝ)^2141 ≤ (8694786771571/20000000000000 : ℝ)^1629 := by
    have hnat : (2652852409 : ℕ)^2141*20000000000000^1629 ≤ 8694786771571^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652852409 5000000000 8694786771571 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413148901/10000000000 : ℝ)^2141 ≤ (44634680764087/100000000000000 : ℝ)^1629 := by
    have hnat : (5413148901 : ℕ)^2141*100000000000000^1629 ≤ 44634680764087^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413148901 10000000000 44634680764087 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1978708907/10000000000 : ℝ)^2141 ≤ (11891385360413/100000000000000 : ℝ)^1629 := by
    have hnat : (1978708907 : ℕ)^2141*100000000000000^1629 ≤ 11891385360413^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978708907 10000000000 11891385360413 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652852409/5000000000 : ℝ), (5413148901/10000000000 : ℝ), (-1978708907/10000000000 : ℝ)] ![(8694786771571/20000000000000 : ℝ), (44634680764087/100000000000000 : ℝ), (11891385360413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652852409/5000000000 : ℝ)|^2141 ≤ (8694786771571/20000000000000 : ℝ)^1629
        have hw : |(2652852409/5000000000 : ℝ)|=(2652852409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413148901/10000000000 : ℝ)|^2141 ≤ (44634680764087/100000000000000 : ℝ)^1629
        have hw : |(5413148901/10000000000 : ℝ)|=(5413148901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1978708907/10000000000 : ℝ)|^2141 ≤ (11891385360413/100000000000000 : ℝ)^1629
        have hw : |(-1978708907/10000000000 : ℝ)|=(1978708907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s6_7 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4331899741/10000000000 : ℝ)*x 0 + (2255248961/5000000000 : ℝ)*x 1 + (4160037111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331899741/10000000000 : ℝ)^2141 ≤ (33303143950331/100000000000000 : ℝ)^1629 := by
    have hnat : (4331899741 : ℕ)^2141*100000000000000^1629 ≤ 33303143950331^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331899741 10000000000 33303143950331 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255248961/5000000000 : ℝ)^2141 ≤ (35119321626247/100000000000000 : ℝ)^1629 := by
    have hnat : (2255248961 : ℕ)^2141*100000000000000^1629 ≤ 35119321626247^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255248961 5000000000 35119321626247 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4160037111/10000000000 : ℝ)^2141 ≤ (15788767207807/50000000000000 : ℝ)^1629 := by
    have hnat : (4160037111 : ℕ)^2141*50000000000000^1629 ≤ 15788767207807^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160037111 10000000000 15788767207807 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331899741/10000000000 : ℝ), (2255248961/5000000000 : ℝ), (4160037111/10000000000 : ℝ)] ![(33303143950331/100000000000000 : ℝ), (35119321626247/100000000000000 : ℝ), (15788767207807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331899741/10000000000 : ℝ)|^2141 ≤ (33303143950331/100000000000000 : ℝ)^1629
        have hw : |(4331899741/10000000000 : ℝ)|=(4331899741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255248961/5000000000 : ℝ)|^2141 ≤ (35119321626247/100000000000000 : ℝ)^1629
        have hw : |(2255248961/5000000000 : ℝ)|=(2255248961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4160037111/10000000000 : ℝ)|^2141 ≤ (15788767207807/50000000000000 : ℝ)^1629
        have hw : |(4160037111/10000000000 : ℝ)|=(4160037111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1322_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11101/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2939/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (919/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2773/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (919/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2773/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (919/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2773/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (919/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2773/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (919/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2773/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (919/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2773/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2773/25000 : ℝ) ^ (4281/1024 : ℝ) ≤ (10174358716458319/100000000000000000000 : ℝ) := by
    have hpowers : (2773/25000 : ℝ)^4281 ≤ (10174358716458319/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2773 : ℕ)^4281*100000000000000000000^1024 ≤ 10174358716458319^1024*25000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2773 25000 10174358716458319 100000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2773/25000 : ℝ)) (X := (10174358716458319/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (919/6250 : ℝ) ^ (4281/1024 : ℝ) ≤ (33061875810940949/100000000000000000000 : ℝ) := by
    have hpowers : (919/6250 : ℝ)^4281 ≤ (33061875810940949/100000000000000000000 : ℝ)^1024 := by
      have hnat : (919 : ℕ)^4281*100000000000000000000^1024 ≤ 33061875810940949^1024*6250^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        919 6250 33061875810940949 100000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (919/6250 : ℝ)) (X := (33061875810940949/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010174358716458319/50000000000000000000 : ℝ) ≤ (10000486696423967/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (50010174358716458319/50000000000000000000 : ℝ)^1024 ≤ (10000486696423967/10000000000000000 : ℝ)^4281 := by
      have hnat : (50010174358716458319 : ℕ)^1024*10000000000000000^4281 ≤ 10000486696423967^4281*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010174358716458319 50000000000000000000 10000486696423967 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000486696423967/10000000000000000 : ℝ)) (X := (50010174358716458319/50000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010809058631849817/25000000000000000000 : ℝ) ≤ (2000206805065229/2000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (25010809058631849817/25000000000000000000 : ℝ)^1024 ≤ (2000206805065229/2000000000000000 : ℝ)^4281 := by
      have hnat : (25010809058631849817 : ℕ)^1024*2000000000000000^4281 ≤ 2000206805065229^4281*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010809058631849817 25000000000000000000 2000206805065229 2000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000206805065229/2000000000000000 : ℝ)) (X := (25010809058631849817/25000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033061875810940949/50000000000000000000 : ℝ) ≤ (10001581354228323/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (50033061875810940949/50000000000000000000 : ℝ)^1024 ≤ (10001581354228323/10000000000000000 : ℝ)^4281 := by
      have hnat : (50033061875810940949 : ℕ)^1024*10000000000000000^4281 ≤ 10001581354228323^4281*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033061875810940949 50000000000000000000 10001581354228323 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001581354228323/10000000000000000 : ℝ)) (X := (50033061875810940949/50000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10174358716458319/100000000000000000000 : ℝ) ≤ ((9027404000779363013/9030000000000000000 : ℝ)+2*(273664451089/180600000000000 : ℝ)*(2773/25000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (9027404000779363013/9030000000000000000 : ℝ)+2*(273664451089/180600000000000 : ℝ)*(2773/25000 : ℝ)=(10000486696423967/10000000000000000 : ℝ) by norm_num, show 1+2*(10174358716458319/100000000000000000000 : ℝ)=(50010174358716458319/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33061875810940949/100000000000000000000 : ℝ)+(10174358716458319/100000000000000000000 : ℝ) ≤ ((9027404000779363013/9030000000000000000 : ℝ)+(273664451089/180600000000000 : ℝ)*((919/6250 : ℝ)+(2773/25000 : ℝ)))^(4281/1024 : ℝ) := by
    rw [show (9027404000779363013/9030000000000000000 : ℝ)+(273664451089/180600000000000 : ℝ)*((919/6250 : ℝ)+(2773/25000 : ℝ))=(2000206805065229/2000000000000000 : ℝ) by norm_num, show 1+(33061875810940949/100000000000000000000 : ℝ)+(10174358716458319/100000000000000000000 : ℝ)=(25010809058631849817/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33061875810940949/100000000000000000000 : ℝ) ≤ ((9027404000779363013/9030000000000000000 : ℝ)+2*(273664451089/180600000000000 : ℝ)*(919/6250 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (9027404000779363013/9030000000000000000 : ℝ)+2*(273664451089/180600000000000 : ℝ)*(919/6250 : ℝ)=(10001581354228323/10000000000000000 : ℝ) by norm_num, show 1+2*(33061875810940949/100000000000000000000 : ℝ)=(50033061875810940949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9027404000779363013/9030000000000000000 : ℝ)*(X 1 0+X 2 0)+(273664451089/180600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (2773/25000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (9027404000779363013/9030000000000000000 : ℝ)) (alpha := (273664451089/180600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9027404000779363013/9030000000000000000 : ℝ)*(X 0 1+X 2 1)+(273664451089/180600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (2773/25000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (9027404000779363013/9030000000000000000 : ℝ)) (alpha := (273664451089/180600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9027404000779363013/9030000000000000000 : ℝ)*(X 0 2+X 1 2)+(273664451089/180600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (2773/25000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (9027404000779363013/9030000000000000000 : ℝ)) (alpha := (273664451089/180600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2061369483/10000000000 : ℝ)*X 0 0+(541375983/1000000000 : ℝ)*X 0 1+(655494489/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674669413/5000000000 : ℝ)*X 1 0+(-536975593/2500000000 : ℝ)*X 1 1+(1048791281/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349339411/10000000000 : ℝ)*X 2 0+(5243955561/10000000000 : ℝ)*X 2 1+(-214790271/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331873599/10000000000 : ℝ)*X 0 0+(2079384489/5000000000 : ℝ)*X 0 1+(56396999/125000000 : ℝ)*X 0 2+(4331873599/10000000000 : ℝ)*X 1 0+(2079384489/5000000000 : ℝ)*X 1 1+(56396999/125000000 : ℝ)*X 1 2+(4331873599/10000000000 : ℝ)*X 2 0+(2079384489/5000000000 : ℝ)*X 2 1+(56396999/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-32209103/156250000 : ℝ)*X 0 0+(5244562847/10000000000 : ℝ)*X 0 1+(1082629849/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305704791/10000000000 : ℝ)*X 1 0+(-1978708659/10000000000 : ℝ)*X 1 1+(5413149109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652852409/5000000000 : ℝ)*X 2 0+(5413148901/10000000000 : ℝ)*X 2 1+(-1978708907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4331899741/10000000000 : ℝ)*X 0 0+(2255248961/5000000000 : ℝ)*X 0 1+(4160037111/10000000000 : ℝ)*X 0 2+(4331899741/10000000000 : ℝ)*X 1 0+(2255248961/5000000000 : ℝ)*X 1 1+(4160037111/10000000000 : ℝ)*X 1 2+(4331899741/10000000000 : ℝ)*X 2 0+(2255248961/5000000000 : ℝ)*X 2 1+(4160037111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (464085779913009976424784633/150500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (345209119/100000000000000 : ℝ)*(base23) + (18964179/25000000000000 : ℝ)*(lower2) + (2973811/20000000000000 : ℝ)*(upper3) + (5644497/20000000000000 : ℝ)*(upper4) + (4361054798184741/100000000000000 : ℝ)*(major0) + (4361054798184741/100000000000000 : ℝ)*(major1) + (4361054798184741/100000000000000 : ℝ)*(major2) + (736144474196559/12500000000000 : ℝ)*(sp0) + (5889172074777107/100000000000000 : ℝ)*(sp1) + (2944579473834651/50000000000000 : ℝ)*(sp2) + (1416467067260643/50000000000000 : ℝ)*(sp3) + (3256240927/20000000000000 : ℝ)*(sp4) + (6390949343/50000000000000 : ℝ)*(sp6) + (3284283527/100000000000000 : ℝ)*(sp7) + (708234354701203/25000000000000 : ℝ)*(f.failure) + (5889172074777107/100000000000000 : ℝ)*(f.sum) + (171900770653267/3010000000000000000000000000 : ℝ)*base66 + (773080454865721789/301000000000000000000000000000000 : ℝ)*base68 + (1715695769985278211/301000000000000000000000000000000 : ℝ)*base69 + (14330800412661721789/301000000000000000000000000000000 : ℝ)*base72 + (11747068170997/3010000000000000000000000000 : ℝ)*base74 + (85956765889278211/301000000000000000000000000000000 : ℝ)*base75 + (2745453052949721789/301000000000000000000000000000000 : ℝ)*base78 + (2215935062668721789/301000000000000000000000000000000 : ℝ)*base80 + (5635608996033/3010000000000000000000000000 : ℝ)*base81 + (366581/625000000000000000000 : ℝ)*base90 + (366581/625000000000000000000 : ℝ)*base92 + (366581/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (118471437118132367098582903/37625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (714866349/25000000000000 : ℝ)*(base19) + (338232643/10000000000000 : ℝ)*(base23) + (268233243/100000000000000 : ℝ)*(upper2) + (28295381/12500000000000 : ℝ)*(upper3) + (327636831/100000000000000 : ℝ)*(upper5) + (2196264245371531/50000000000000 : ℝ)*(major0) + (2196264245371531/50000000000000 : ℝ)*(major1) + (2196264245371531/50000000000000 : ℝ)*(major2) + (59373737797/100000000000000 : ℝ)*(sp1) + (57806761117/100000000000000 : ℝ)*(sp2) + (5931674174303819/100000000000000 : ℝ)*(sp4) + (2965805970550313/50000000000000 : ℝ)*(sp5) + (370725811576017/6250000000000 : ℝ)*(sp6) + (1426691351112107/50000000000000 : ℝ)*(sp7) + (1426691351112107/50000000000000 : ℝ)*(f.failure) + (5931674174303819/100000000000000 : ℝ)*(f.sum) + (10359833365631/4515000000000000000000000000 : ℝ)*base66 + (6528627589383967097/451500000000000000000000000000000 : ℝ)*base68 + (4471853837595967097/451500000000000000000000000000000 : ℝ)*base70 + (6172546723925467097/451500000000000000000000000000000 : ℝ)*base72 + (10998247882091/4515000000000000000000000000 : ℝ)*base74 + (1280474975558032903/451500000000000000000000000000000 : ℝ)*base75 + (1267349179317967097/451500000000000000000000000000000 : ℝ)*base78 + (3682925135607967097/451500000000000000000000000000000 : ℝ)*base80 + (8930087522441/4515000000000000000000000000 : ℝ)*base82 + (16500211/1250000000000000000000 : ℝ)*base89 + (16500211/1250000000000000000000 : ℝ)*base91 + (16500211/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1322_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1322_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1322_s7_0 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-412275417/2000000000 : ℝ)*x 0 + (676710361/1250000000 : ℝ)*x 1 + (131100699/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412275417/2000000000 : ℝ)^2141 ≤ (501943562279/4000000000000 : ℝ)^1629 := by
    have hnat : (412275417 : ℕ)^2141*4000000000000^1629 ≤ 501943562279^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412275417 2000000000 501943562279 4000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676710361/1250000000 : ℝ)^2141 ≤ (22320233895213/50000000000000 : ℝ)^1629 := by
    have hnat : (676710361 : ℕ)^2141*50000000000000^1629 ≤ 22320233895213^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676710361 1250000000 22320233895213 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131100699/250000000 : ℝ)^2141 ≤ (42810943136603/100000000000000 : ℝ)^1629 := by
    have hnat : (131100699 : ℕ)^2141*100000000000000^1629 ≤ 42810943136603^1629*250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131100699 250000000 42810943136603 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412275417/2000000000 : ℝ), (676710361/1250000000 : ℝ), (131100699/250000000 : ℝ)] ![(501943562279/4000000000000 : ℝ), (22320233895213/50000000000000 : ℝ), (42810943136603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412275417/2000000000 : ℝ)|^2141 ≤ (501943562279/4000000000000 : ℝ)^1629
        have hw : |(-412275417/2000000000 : ℝ)|=(412275417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676710361/1250000000 : ℝ)|^2141 ≤ (22320233895213/50000000000000 : ℝ)^1629
        have hw : |(676710361/1250000000 : ℝ)|=(676710361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131100699/250000000 : ℝ)|^2141 ≤ (42810943136603/100000000000000 : ℝ)^1629
        have hw : |(131100699/250000000 : ℝ)|=(131100699/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s7_1 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337330001/2500000000 : ℝ)*x 0 + (-2147832729/10000000000 : ℝ)*x 1 + (327751747/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337330001/2500000000 : ℝ)^2141 ≤ (8788847599553/20000000000000 : ℝ)^1629 := by
    have hnat : (1337330001 : ℕ)^2141*20000000000000^1629 ≤ 8788847599553^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337330001 2500000000 8788847599553 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147832729/10000000000 : ℝ)^2141 ≤ (165560236797/1250000000000 : ℝ)^1629 := by
    have hnat : (2147832729 : ℕ)^2141*1250000000000^1629 ≤ 165560236797^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147832729 10000000000 165560236797 1250000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327751747/625000000 : ℝ)^2141 ≤ (21405471525383/50000000000000 : ℝ)^1629 := by
    have hnat : (327751747 : ℕ)^2141*50000000000000^1629 ≤ 21405471525383^1629*625000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327751747 625000000 21405471525383 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337330001/2500000000 : ℝ), (-2147832729/10000000000 : ℝ), (327751747/625000000 : ℝ)] ![(8788847599553/20000000000000 : ℝ), (165560236797/1250000000000 : ℝ), (21405471525383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337330001/2500000000 : ℝ)|^2141 ≤ (8788847599553/20000000000000 : ℝ)^1629
        have hw : |(1337330001/2500000000 : ℝ)|=(1337330001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2147832729/10000000000 : ℝ)|^2141 ≤ (165560236797/1250000000000 : ℝ)^1629
        have hw : |(-2147832729/10000000000 : ℝ)|=(2147832729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327751747/625000000 : ℝ)|^2141 ≤ (21405471525383/50000000000000 : ℝ)^1629
        have hw : |(327751747/625000000 : ℝ)|=(327751747/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s7_2 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349319999/10000000000 : ℝ)*x 0 + (2622013983/5000000000 : ℝ)*x 1 + (-536958179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349319999/10000000000 : ℝ)^2141 ≤ (2197211897189/5000000000000 : ℝ)^1629 := by
    have hnat : (5349319999 : ℕ)^2141*5000000000000^1629 ≤ 2197211897189^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349319999 10000000000 2197211897189 5000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622013983/5000000000 : ℝ)^2141 ≤ (42810943200981/100000000000000 : ℝ)^1629 := by
    have hnat : (2622013983 : ℕ)^2141*100000000000000^1629 ≤ 42810943200981^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622013983 5000000000 42810943200981 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536958179/2500000000 : ℝ)^2141 ≤ (6622409419199/50000000000000 : ℝ)^1629 := by
    have hnat : (536958179 : ℕ)^2141*50000000000000^1629 ≤ 6622409419199^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536958179 2500000000 6622409419199 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349319999/10000000000 : ℝ), (2622013983/5000000000 : ℝ), (-536958179/2500000000 : ℝ)] ![(2197211897189/5000000000000 : ℝ), (42810943200981/100000000000000 : ℝ), (6622409419199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349319999/10000000000 : ℝ)|^2141 ≤ (2197211897189/5000000000000 : ℝ)^1629
        have hw : |(5349319999/10000000000 : ℝ)|=(5349319999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622013983/5000000000 : ℝ)|^2141 ≤ (42810943200981/100000000000000 : ℝ)^1629
        have hw : |(2622013983/5000000000 : ℝ)|=(2622013983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-536958179/2500000000 : ℝ)|^2141 ≤ (6622409419199/50000000000000 : ℝ)^1629
        have hw : |(-536958179/2500000000 : ℝ)|=(536958179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s7_3 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4331879003/10000000000 : ℝ)*x 0 + (2079461283/5000000000 : ℝ)*x 1 + (2255802439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331879003/10000000000 : ℝ)^2141 ≤ (16651467204677/50000000000000 : ℝ)^1629 := by
    have hnat : (4331879003 : ℕ)^2141*50000000000000^1629 ≤ 16651467204677^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331879003 10000000000 16651467204677 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079461283/5000000000 : ℝ)^2141 ≤ (31566415666873/100000000000000 : ℝ)^1629 := by
    have hnat : (2079461283 : ℕ)^2141*100000000000000^1629 ≤ 31566415666873^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079461283 5000000000 31566415666873 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255802439/5000000000 : ℝ)^2141 ≤ (17565324957643/50000000000000 : ℝ)^1629 := by
    have hnat : (2255802439 : ℕ)^2141*50000000000000^1629 ≤ 17565324957643^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255802439 5000000000 17565324957643 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331879003/10000000000 : ℝ), (2079461283/5000000000 : ℝ), (2255802439/5000000000 : ℝ)] ![(16651467204677/50000000000000 : ℝ), (31566415666873/100000000000000 : ℝ), (17565324957643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331879003/10000000000 : ℝ)|^2141 ≤ (16651467204677/50000000000000 : ℝ)^1629
        have hw : |(4331879003/10000000000 : ℝ)|=(4331879003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079461283/5000000000 : ℝ)|^2141 ≤ (31566415666873/100000000000000 : ℝ)^1629
        have hw : |(2079461283/5000000000 : ℝ)|=(2079461283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255802439/5000000000 : ℝ)|^2141 ≤ (17565324957643/50000000000000 : ℝ)^1629
        have hw : |(2255802439/5000000000 : ℝ)|=(2255802439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s7_4 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2061389611/10000000000 : ℝ)*x 0 + (5244633893/10000000000 : ℝ)*x 1 + (5413073719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061389611/10000000000 : ℝ)^2141 ≤ (2509737855001/20000000000000 : ℝ)^1629 := by
    have hnat : (2061389611 : ℕ)^2141*20000000000000^1629 ≤ 2509737855001^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061389611 10000000000 2509737855001 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244633893/10000000000 : ℝ)^2141 ≤ (42817444701041/100000000000000 : ℝ)^1629 := by
    have hnat : (5244633893 : ℕ)^2141*100000000000000^1629 ≤ 42817444701041^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244633893 10000000000 42817444701041 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413073719/10000000000 : ℝ)^2141 ≤ (8926773200341/20000000000000 : ℝ)^1629 := by
    have hnat : (5413073719 : ℕ)^2141*20000000000000^1629 ≤ 8926773200341^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413073719 10000000000 8926773200341 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2061389611/10000000000 : ℝ), (5244633893/10000000000 : ℝ), (5413073719/10000000000 : ℝ)] ![(2509737855001/20000000000000 : ℝ), (42817444701041/100000000000000 : ℝ), (8926773200341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2061389611/10000000000 : ℝ)|^2141 ≤ (2509737855001/20000000000000 : ℝ)^1629
        have hw : |(-2061389611/10000000000 : ℝ)|=(2061389611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244633893/10000000000 : ℝ)|^2141 ≤ (42817444701041/100000000000000 : ℝ)^1629
        have hw : |(5244633893/10000000000 : ℝ)|=(5244633893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413073719/10000000000 : ℝ)|^2141 ≤ (8926773200341/20000000000000 : ℝ)^1629
        have hw : |(5413073719/10000000000 : ℝ)|=(5413073719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s7_5 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061144647/2000000000 : ℝ)*x 0 + (-123674187/625000000 : ℝ)*x 1 + (5413073689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061144647/2000000000 : ℝ)^2141 ≤ (8694826438681/20000000000000 : ℝ)^1629 := by
    have hnat : (1061144647 : ℕ)^2141*20000000000000^1629 ≤ 8694826438681^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061144647 2000000000 8694826438681 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123674187/625000000 : ℝ)^2141 ≤ (11892002120747/100000000000000 : ℝ)^1629 := by
    have hnat : (123674187 : ℕ)^2141*100000000000000^1629 ≤ 11892002120747^1629*625000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123674187 625000000 11892002120747 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413073689/10000000000 : ℝ)^2141 ≤ (4463386567659/10000000000000 : ℝ)^1629 := by
    have hnat : (5413073689 : ℕ)^2141*10000000000000^1629 ≤ 4463386567659^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413073689 10000000000 4463386567659 10000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061144647/2000000000 : ℝ), (-123674187/625000000 : ℝ), (5413073689/10000000000 : ℝ)] ![(8694826438681/20000000000000 : ℝ), (11892002120747/100000000000000 : ℝ), (4463386567659/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061144647/2000000000 : ℝ)|^2141 ≤ (8694826438681/20000000000000 : ℝ)^1629
        have hw : |(1061144647/2000000000 : ℝ)|=(1061144647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123674187/625000000 : ℝ)|^2141 ≤ (11892002120747/100000000000000 : ℝ)^1629
        have hw : |(-123674187/625000000 : ℝ)|=(123674187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413073689/10000000000 : ℝ)|^2141 ≤ (4463386567659/10000000000000 : ℝ)^1629
        have hw : |(5413073689/10000000000 : ℝ)|=(5413073689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s7_6 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212228931/400000000 : ℝ)*x 0 + (5413073631/10000000000 : ℝ)*x 1 + (-247348377/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212228931/400000000 : ℝ)^2141 ≤ (43474132624171/100000000000000 : ℝ)^1629 := by
    have hnat : (212228931 : ℕ)^2141*100000000000000^1629 ≤ 43474132624171^1629*400000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212228931 400000000 43474132624171 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413073631/10000000000 : ℝ)^2141 ≤ (44633865048033/100000000000000 : ℝ)^1629 := by
    have hnat : (5413073631 : ℕ)^2141*100000000000000^1629 ≤ 44633865048033^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413073631 10000000000 44633865048033 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247348377/1250000000 : ℝ)^2141 ≤ (5946001155157/50000000000000 : ℝ)^1629 := by
    have hnat : (247348377 : ℕ)^2141*50000000000000^1629 ≤ 5946001155157^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247348377 1250000000 5946001155157 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212228931/400000000 : ℝ), (5413073631/10000000000 : ℝ), (-247348377/1250000000 : ℝ)] ![(43474132624171/100000000000000 : ℝ), (44633865048033/100000000000000 : ℝ), (5946001155157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212228931/400000000 : ℝ)|^2141 ≤ (43474132624171/100000000000000 : ℝ)^1629
        have hw : |(212228931/400000000 : ℝ)|=(212228931/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413073631/10000000000 : ℝ)|^2141 ≤ (44633865048033/100000000000000 : ℝ)^1629
        have hw : |(5413073631/10000000000 : ℝ)|=(5413073631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-247348377/1250000000 : ℝ)|^2141 ≤ (5946001155157/50000000000000 : ℝ)^1629
        have hw : |(-247348377/1250000000 : ℝ)|=(247348377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s7_7 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (541488093/1250000000 : ℝ)*x 0 + (4510345053/10000000000 : ℝ)*x 1 + (2080094423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541488093/1250000000 : ℝ)^2141 ≤ (3330319450171/10000000000000 : ℝ)^1629 := by
    have hnat : (541488093 : ℕ)^2141*10000000000000^1629 ≤ 3330319450171^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541488093 1250000000 3330319450171 10000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510345053/10000000000 : ℝ)^2141 ≤ (35117757274809/100000000000000 : ℝ)^1629 := by
    have hnat : (4510345053 : ℕ)^2141*100000000000000^1629 ≤ 35117757274809^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510345053 10000000000 35117757274809 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080094423/5000000000 : ℝ)^2141 ≤ (31579048202901/100000000000000 : ℝ)^1629 := by
    have hnat : (2080094423 : ℕ)^2141*100000000000000^1629 ≤ 31579048202901^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080094423 5000000000 31579048202901 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541488093/1250000000 : ℝ), (4510345053/10000000000 : ℝ), (2080094423/5000000000 : ℝ)] ![(3330319450171/10000000000000 : ℝ), (35117757274809/100000000000000 : ℝ), (31579048202901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541488093/1250000000 : ℝ)|^2141 ≤ (3330319450171/10000000000000 : ℝ)^1629
        have hw : |(541488093/1250000000 : ℝ)|=(541488093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510345053/10000000000 : ℝ)|^2141 ≤ (35117757274809/100000000000000 : ℝ)^1629
        have hw : |(4510345053/10000000000 : ℝ)|=(4510345053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2080094423/5000000000 : ℝ)|^2141 ≤ (31579048202901/100000000000000 : ℝ)^1629
        have hw : |(2080094423/5000000000 : ℝ)|=(2080094423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1322_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5551/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14693/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2939/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2939/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2939/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2939/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2939/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2939/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11101/100000 : ℝ) ^ (4281/1024 : ℝ) ≤ (5104458228620073/50000000000000000000 : ℝ) := by
    have hpowers : (11101/100000 : ℝ)^4281 ≤ (5104458228620073/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11101 : ℕ)^4281*50000000000000000000^1024 ≤ 5104458228620073^1024*100000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11101 100000 5104458228620073 50000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11101/100000 : ℝ)) (X := (5104458228620073/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2939/20000 : ℝ) ^ (4281/1024 : ℝ) ≤ (16488678146290381/50000000000000000000 : ℝ) := by
    have hpowers : (2939/20000 : ℝ)^4281 ≤ (16488678146290381/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2939 : ℕ)^4281*50000000000000000000^1024 ≤ 16488678146290381^1024*20000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2939 20000 16488678146290381 50000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2939/20000 : ℝ)) (X := (16488678146290381/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005104458228620073/25000000000000000000 : ℝ) ≤ (1250061043673177/1250000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (25005104458228620073/25000000000000000000 : ℝ)^1024 ≤ (1250061043673177/1250000000000000 : ℝ)^4281 := by
      have hnat : (25005104458228620073 : ℕ)^1024*1250000000000000^4281 ≤ 1250061043673177^4281*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005104458228620073 25000000000000000000 1250061043673177 1250000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250061043673177/1250000000000000 : ℝ)) (X := (25005104458228620073/25000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010796568187455227/25000000000000000000 : ℝ) ≤ (10001032830650897/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (25010796568187455227/25000000000000000000 : ℝ)^1024 ≤ (10001032830650897/10000000000000000 : ℝ)^4281 := by
      have hnat : (25010796568187455227 : ℕ)^1024*10000000000000000^4281 ≤ 10001032830650897^4281*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010796568187455227 25000000000000000000 10001032830650897 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001032830650897/10000000000000000 : ℝ)) (X := (25010796568187455227/25000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016488678146290381/25000000000000000000 : ℝ) ≤ (5000788655958189/5000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (25016488678146290381/25000000000000000000 : ℝ)^1024 ≤ (5000788655958189/5000000000000000 : ℝ)^4281 := by
      have hnat : (25016488678146290381 : ℕ)^1024*5000000000000000^4281 ≤ 5000788655958189^4281*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016488678146290381 25000000000000000000 5000788655958189 5000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000788655958189/5000000000000000 : ℝ)) (X := (25016488678146290381/25000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5104458228620073/50000000000000000000 : ℝ) ≤ ((17964833277317487971/17970000000000000000 : ℝ)+2*(544481265481/359400000000000 : ℝ)*(11101/100000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (17964833277317487971/17970000000000000000 : ℝ)+2*(544481265481/359400000000000 : ℝ)*(11101/100000 : ℝ)=(1250061043673177/1250000000000000 : ℝ) by norm_num, show 1+2*(5104458228620073/50000000000000000000 : ℝ)=(25005104458228620073/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16488678146290381/50000000000000000000 : ℝ)+(5104458228620073/50000000000000000000 : ℝ) ≤ ((17964833277317487971/17970000000000000000 : ℝ)+(544481265481/359400000000000 : ℝ)*((2939/20000 : ℝ)+(11101/100000 : ℝ)))^(4281/1024 : ℝ) := by
    rw [show (17964833277317487971/17970000000000000000 : ℝ)+(544481265481/359400000000000 : ℝ)*((2939/20000 : ℝ)+(11101/100000 : ℝ))=(10001032830650897/10000000000000000 : ℝ) by norm_num, show 1+(16488678146290381/50000000000000000000 : ℝ)+(5104458228620073/50000000000000000000 : ℝ)=(25010796568187455227/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16488678146290381/50000000000000000000 : ℝ) ≤ ((17964833277317487971/17970000000000000000 : ℝ)+2*(544481265481/359400000000000 : ℝ)*(2939/20000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (17964833277317487971/17970000000000000000 : ℝ)+2*(544481265481/359400000000000 : ℝ)*(2939/20000 : ℝ)=(5000788655958189/5000000000000000 : ℝ) by norm_num, show 1+2*(16488678146290381/50000000000000000000 : ℝ)=(25016488678146290381/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17964833277317487971/17970000000000000000 : ℝ)*(X 1 0+X 2 0)+(544481265481/359400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (17964833277317487971/17970000000000000000 : ℝ)) (alpha := (544481265481/359400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17964833277317487971/17970000000000000000 : ℝ)*(X 0 1+X 2 1)+(544481265481/359400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (17964833277317487971/17970000000000000000 : ℝ)) (alpha := (544481265481/359400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17964833277317487971/17970000000000000000 : ℝ)*(X 0 2+X 1 2)+(544481265481/359400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (17964833277317487971/17970000000000000000 : ℝ)) (alpha := (544481265481/359400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-412275417/2000000000 : ℝ)*X 0 0+(676710361/1250000000 : ℝ)*X 0 1+(131100699/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337330001/2500000000 : ℝ)*X 1 0+(-2147832729/10000000000 : ℝ)*X 1 1+(327751747/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349319999/10000000000 : ℝ)*X 2 0+(2622013983/5000000000 : ℝ)*X 2 1+(-536958179/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331879003/10000000000 : ℝ)*X 0 0+(2079461283/5000000000 : ℝ)*X 0 1+(2255802439/5000000000 : ℝ)*X 0 2+(4331879003/10000000000 : ℝ)*X 1 0+(2079461283/5000000000 : ℝ)*X 1 1+(2255802439/5000000000 : ℝ)*X 1 2+(4331879003/10000000000 : ℝ)*X 2 0+(2079461283/5000000000 : ℝ)*X 2 1+(2255802439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2061389611/10000000000 : ℝ)*X 0 0+(5244633893/10000000000 : ℝ)*X 0 1+(5413073719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061144647/2000000000 : ℝ)*X 1 0+(-123674187/625000000 : ℝ)*X 1 1+(5413073689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212228931/400000000 : ℝ)*X 2 0+(5413073631/10000000000 : ℝ)*X 2 1+(-247348377/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((541488093/1250000000 : ℝ)*X 0 0+(4510345053/10000000000 : ℝ)*X 0 1+(2080094423/5000000000 : ℝ)*X 0 2+(541488093/1250000000 : ℝ)*X 1 0+(4510345053/10000000000 : ℝ)*X 1 1+(2080094423/5000000000 : ℝ)*X 1 2+(541488093/1250000000 : ℝ)*X 2 0+(4510345053/10000000000 : ℝ)*X 2 1+(2080094423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13735639369350826378258509/1871875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1395302991/100000000000000 : ℝ)*(base19) + (1305466727/100000000000000 : ℝ)*(base23) + (9021821/20000000000000 : ℝ)*(lower2) + (172164159/100000000000000 : ℝ)*(upper3) + (123985471/100000000000000 : ℝ)*(upper5) + (27280676485707/625000000000 : ℝ)*(major0) + (27280676485707/625000000000 : ℝ)*(major1) + (27280676485707/625000000000 : ℝ)*(major2) + (5894346828690751/100000000000000 : ℝ)*(sp0) + (73679677821779/1250000000000 : ℝ)*(sp1) + (1178874863115717/20000000000000 : ℝ)*(sp2) + (283542621777577/10000000000000 : ℝ)*(sp3) + (28792354561/100000000000000 : ℝ)*(sp4) + (14392008341/100000000000000 : ℝ)*(sp7) + (2835440609784111/100000000000000 : ℝ)*(f.failure) + (92099619078833/1562500000000 : ℝ)*(f.sum) + (273887862829/74875000000000000000000000 : ℝ)*base65 + (37402148126555999/3743750000000000000000000000000 : ℝ)*base67 + (31750084792249749/3743750000000000000000000000000 : ℝ)*base69 + (37272694717430999/3743750000000000000000000000000 : ℝ)*base71 + (1387803019163/599000000000000000000000000 : ℝ)*base74 + (56784360140505999/3743750000000000000000000000000 : ℝ)*base75 + (7804694537024749/3743750000000000000000000000000 : ℝ)*base77 + (62918038463112249/3743750000000000000000000000000 : ℝ)*base79 + (27885160089/59900000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (17102697/2500000000000000000000 : ℝ)*base90 + (17102697/2500000000000000000000 : ℝ)*base92 + (17102697/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (626312609817588994016921399/149750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (985554293/100000000000000 : ℝ)*(base19) + (1148090787/100000000000000 : ℝ)*(base23) + (161848237/50000000000000 : ℝ)*(lower1) + (1236179/2000000000000 : ℝ)*(upper2) + (110559557/100000000000000 : ℝ)*(upper3) + (80876073/50000000000000 : ℝ)*(upper5) + (4396338986021531/100000000000000 : ℝ)*(major0) + (4396338986021531/100000000000000 : ℝ)*(major1) + (4396338986021531/100000000000000 : ℝ)*(major2) + (156236649/100000000000000 : ℝ)*(sp2) + (5936819835974143/100000000000000 : ℝ)*(sp4) + (5936818850419851/100000000000000 : ℝ)*(sp5) + (1484204632911677/25000000000000 : ℝ)*(sp6) + (114234319866239/4000000000000 : ℝ)*(sp7) + (114234319866239/4000000000000 : ℝ)*(f.failure) + (5936819835974143/100000000000000 : ℝ)*(f.sum) + (28237095096221/17970000000000000000000000000 : ℝ)*base65 + (25547671451732053601/1797000000000000000000000000000000 : ℝ)*base67 + (6163374421211053601/1797000000000000000000000000000000 : ℝ)*base69 + (15511942170965053601/1797000000000000000000000000000000 : ℝ)*base71 + (15781253281901/17970000000000000000000000000 : ℝ)*base73 + (25849376460822946399/1797000000000000000000000000000000 : ℝ)*base76 + (14021808554363053601/1797000000000000000000000000000000 : ℝ)*base77 + (8110564644281053601/1797000000000000000000000000000000 : ℝ)*base79 + (217065728927449/17970000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (398247/100000000000000000000 : ℝ)*base89 + (398247/100000000000000000000 : ℝ)*base91 + (398247/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1322_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5551/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1322_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1322_box_0 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1892515663/10000000000 : ℝ)*x 0 + (5390773821/10000000000 : ℝ)*x 1 + (1078154713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1892515663/10000000000 : ℝ)^2141 ≤ (11215293405173/100000000000000 : ℝ)^1629 := by
    have hnat : (1892515663 : ℕ)^2141*100000000000000^1629 ≤ 11215293405173^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892515663 10000000000 11215293405173 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390773821/10000000000 : ℝ)^2141 ≤ (22196177338187/50000000000000 : ℝ)^1629 := by
    have hnat : (5390773821 : ℕ)^2141*50000000000000^1629 ≤ 22196177338187^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390773821 10000000000 22196177338187 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078154713/2000000000 : ℝ)^2141 ≤ (22196175952827/50000000000000 : ℝ)^1629 := by
    have hnat : (1078154713 : ℕ)^2141*50000000000000^1629 ≤ 22196175952827^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078154713 2000000000 22196175952827 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1892515663/10000000000 : ℝ), (5390773821/10000000000 : ℝ), (1078154713/2000000000 : ℝ)] ![(11215293405173/100000000000000 : ℝ), (22196177338187/50000000000000 : ℝ), (22196175952827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1892515663/10000000000 : ℝ)|^2141 ≤ (11215293405173/100000000000000 : ℝ)^1629
        have hw : |(-1892515663/10000000000 : ℝ)|=(1892515663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390773821/10000000000 : ℝ)|^2141 ≤ (22196177338187/50000000000000 : ℝ)^1629
        have hw : |(5390773821/10000000000 : ℝ)|=(5390773821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078154713/2000000000 : ℝ)|^2141 ≤ (22196175952827/50000000000000 : ℝ)^1629
        have hw : |(1078154713/2000000000 : ℝ)|=(1078154713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_1 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41288059/78125000 : ℝ)*x 0 + (-1018751443/5000000000 : ℝ)*x 1 + (2695387111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41288059/78125000 : ℝ)^2141 ≤ (5406214481563/12500000000000 : ℝ)^1629 := by
    have hnat : (41288059 : ℕ)^2141*12500000000000^1629 ≤ 5406214481563^1629*78125000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41288059 78125000 5406214481563 12500000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018751443/5000000000 : ℝ)^2141 ≤ (2471585022923/20000000000000 : ℝ)^1629 := by
    have hnat : (1018751443 : ℕ)^2141*20000000000000^1629 ≤ 2471585022923^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018751443 5000000000 2471585022923 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695387111/5000000000 : ℝ)^2141 ≤ (44392359016447/100000000000000 : ℝ)^1629 := by
    have hnat : (2695387111 : ℕ)^2141*100000000000000^1629 ≤ 44392359016447^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695387111 5000000000 44392359016447 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41288059/78125000 : ℝ), (-1018751443/5000000000 : ℝ), (2695387111/5000000000 : ℝ)] ![(5406214481563/12500000000000 : ℝ), (2471585022923/20000000000000 : ℝ), (44392359016447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41288059/78125000 : ℝ)|^2141 ≤ (5406214481563/12500000000000 : ℝ)^1629
        have hw : |(41288059/78125000 : ℝ)|=(41288059/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1018751443/5000000000 : ℝ)|^2141 ≤ (2471585022923/20000000000000 : ℝ)^1629
        have hw : |(-1018751443/5000000000 : ℝ)|=(1018751443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695387111/5000000000 : ℝ)|^2141 ≤ (44392359016447/100000000000000 : ℝ)^1629
        have hw : |(2695387111/5000000000 : ℝ)|=(2695387111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_2 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5284871937/10000000000 : ℝ)*x 0 + (5390773941/10000000000 : ℝ)*x 1 + (-2037502749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284871937/10000000000 : ℝ)^2141 ≤ (43249719993503/100000000000000 : ℝ)^1629 := by
    have hnat : (5284871937 : ℕ)^2141*100000000000000^1629 ≤ 43249719993503^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284871937 10000000000 43249719993503 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390773941/10000000000 : ℝ)^2141 ≤ (44392355975149/100000000000000 : ℝ)^1629 := by
    have hnat : (5390773941 : ℕ)^2141*100000000000000^1629 ≤ 44392355975149^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390773941 10000000000 44392355975149 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2037502749/10000000000 : ℝ)^2141 ≤ (772370251407/6250000000000 : ℝ)^1629 := by
    have hnat : (2037502749 : ℕ)^2141*6250000000000^1629 ≤ 772370251407^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037502749 10000000000 772370251407 6250000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284871937/10000000000 : ℝ), (5390773941/10000000000 : ℝ), (-2037502749/10000000000 : ℝ)] ![(43249719993503/100000000000000 : ℝ), (44392355975149/100000000000000 : ℝ), (772370251407/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284871937/10000000000 : ℝ)|^2141 ≤ (43249719993503/100000000000000 : ℝ)^1629
        have hw : |(5284871937/10000000000 : ℝ)|=(5284871937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390773941/10000000000 : ℝ)|^2141 ≤ (44392355975149/100000000000000 : ℝ)^1629
        have hw : |(5390773941/10000000000 : ℝ)|=(5390773941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2037502749/10000000000 : ℝ)|^2141 ≤ (772370251407/6250000000000 : ℝ)^1629
        have hw : |(-2037502749/10000000000 : ℝ)|=(2037502749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_3 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (224027481/500000000 : ℝ)*x 0 + (133171197/312500000 : ℝ)*x 1 + (4261478117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224027481/500000000 : ℝ)^2141 ≤ (34813170873257/100000000000000 : ℝ)^1629 := by
    have hnat : (224027481 : ℕ)^2141*100000000000000^1629 ≤ 34813170873257^1629*500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224027481 500000000 34813170873257 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133171197/312500000 : ℝ)^2141 ≤ (32593415497309/100000000000000 : ℝ)^1629 := by
    have hnat : (133171197 : ℕ)^2141*100000000000000^1629 ≤ 32593415497309^1629*312500000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133171197 312500000 32593415497309 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4261478117/10000000000 : ℝ)^2141 ≤ (3259341361753/10000000000000 : ℝ)^1629 := by
    have hnat : (4261478117 : ℕ)^2141*10000000000000^1629 ≤ 3259341361753^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261478117 10000000000 3259341361753 10000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(224027481/500000000 : ℝ), (133171197/312500000 : ℝ), (4261478117/10000000000 : ℝ)] ![(34813170873257/100000000000000 : ℝ), (32593415497309/100000000000000 : ℝ), (3259341361753/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(224027481/500000000 : ℝ)|^2141 ≤ (34813170873257/100000000000000 : ℝ)^1629
        have hw : |(224027481/500000000 : ℝ)|=(224027481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(133171197/312500000 : ℝ)|^2141 ≤ (32593415497309/100000000000000 : ℝ)^1629
        have hw : |(133171197/312500000 : ℝ)|=(133171197/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4261478117/10000000000 : ℝ)|^2141 ≤ (3259341361753/10000000000000 : ℝ)^1629
        have hw : |(4261478117/10000000000 : ℝ)|=(4261478117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_4 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1116499551/5000000000 : ℝ)*x 0 + (5264462547/10000000000 : ℝ)*x 1 + (2632231143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1116499551/5000000000 : ℝ)^2141 ≤ (2787867290721/20000000000000 : ℝ)^1629 := by
    have hnat : (1116499551 : ℕ)^2141*20000000000000^1629 ≤ 2787867290721^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116499551 5000000000 2787867290721 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264462547/10000000000 : ℝ)^2141 ≤ (21515166581247/50000000000000 : ℝ)^1629 := by
    have hnat : (5264462547 : ℕ)^2141*50000000000000^1629 ≤ 21515166581247^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264462547 10000000000 21515166581247 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632231143/5000000000 : ℝ)^2141 ≤ (5378791294829/12500000000000 : ℝ)^1629 := by
    have hnat : (2632231143 : ℕ)^2141*12500000000000^1629 ≤ 5378791294829^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632231143 5000000000 5378791294829 12500000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1116499551/5000000000 : ℝ), (5264462547/10000000000 : ℝ), (2632231143/5000000000 : ℝ)] ![(2787867290721/20000000000000 : ℝ), (21515166581247/50000000000000 : ℝ), (5378791294829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1116499551/5000000000 : ℝ)|^2141 ≤ (2787867290721/20000000000000 : ℝ)^1629
        have hw : |(-1116499551/5000000000 : ℝ)|=(1116499551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264462547/10000000000 : ℝ)|^2141 ≤ (21515166581247/50000000000000 : ℝ)^1629
        have hw : |(5264462547/10000000000 : ℝ)|=(5264462547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632231143/5000000000 : ℝ)|^2141 ≤ (5378791294829/12500000000000 : ℝ)^1629
        have hw : |(2632231143/5000000000 : ℝ)|=(2632231143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_5 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074733249/2000000000 : ℝ)*x 0 + (-20880447/100000000 : ℝ)*x 1 + (2632230973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074733249/2000000000 : ℝ)^2141 ≤ (11051822415051/25000000000000 : ℝ)^1629 := by
    have hnat : (1074733249 : ℕ)^2141*25000000000000^1629 ≤ 11051822415051^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074733249 2000000000 11051822415051 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20880447/100000000 : ℝ)^2141 ≤ (12762383622963/100000000000000 : ℝ)^1629 := by
    have hnat : (20880447 : ℕ)^2141*100000000000000^1629 ≤ 12762383622963^1629*100000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20880447 100000000 12762383622963 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632230973/5000000000 : ℝ)^2141 ≤ (4303032670609/10000000000000 : ℝ)^1629 := by
    have hnat : (2632230973 : ℕ)^2141*10000000000000^1629 ≤ 4303032670609^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632230973 5000000000 4303032670609 10000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074733249/2000000000 : ℝ), (-20880447/100000000 : ℝ), (2632230973/5000000000 : ℝ)] ![(11051822415051/25000000000000 : ℝ), (12762383622963/100000000000000 : ℝ), (4303032670609/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074733249/2000000000 : ℝ)|^2141 ≤ (11051822415051/25000000000000 : ℝ)^1629
        have hw : |(1074733249/2000000000 : ℝ)|=(1074733249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20880447/100000000 : ℝ)|^2141 ≤ (12762383622963/100000000000000 : ℝ)^1629
        have hw : |(-20880447/100000000 : ℝ)|=(20880447/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632230973/5000000000 : ℝ)|^2141 ≤ (4303032670609/10000000000000 : ℝ)^1629
        have hw : |(2632230973/5000000000 : ℝ)|=(2632230973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_6 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5373666277/10000000000 : ℝ)*x 0 + (1316115577/2500000000 : ℝ)*x 1 + (-522011043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373666277/10000000000 : ℝ)^2141 ≤ (44207290006199/100000000000000 : ℝ)^1629 := by
    have hnat : (5373666277 : ℕ)^2141*100000000000000^1629 ≤ 44207290006199^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373666277 10000000000 44207290006199 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316115577/2500000000 : ℝ)^2141 ≤ (43030330594973/100000000000000 : ℝ)^1629 := by
    have hnat : (1316115577 : ℕ)^2141*100000000000000^1629 ≤ 43030330594973^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316115577 2500000000 43030330594973 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522011043/2500000000 : ℝ)^2141 ≤ (12762379381443/100000000000000 : ℝ)^1629 := by
    have hnat : (522011043 : ℕ)^2141*100000000000000^1629 ≤ 12762379381443^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522011043 2500000000 12762379381443 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373666277/10000000000 : ℝ), (1316115577/2500000000 : ℝ), (-522011043/2500000000 : ℝ)] ![(44207290006199/100000000000000 : ℝ), (43030330594973/100000000000000 : ℝ), (12762379381443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373666277/10000000000 : ℝ)|^2141 ≤ (44207290006199/100000000000000 : ℝ)^1629
        have hw : |(5373666277/10000000000 : ℝ)|=(5373666277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316115577/2500000000 : ℝ)|^2141 ≤ (43030330594973/100000000000000 : ℝ)^1629
        have hw : |(1316115577/2500000000 : ℝ)|=(1316115577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522011043/2500000000 : ℝ)|^2141 ≤ (12762379381443/100000000000000 : ℝ)^1629
        have hw : |(-522011043/2500000000 : ℝ)|=(522011043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_7 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2091156207/5000000000 : ℝ)*x 0 + (1102635551/2500000000 : ℝ)*x 1 + (2205271429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091156207/5000000000 : ℝ)^2141 ≤ (254399599397/800000000000 : ℝ)^1629 := by
    have hnat : (2091156207 : ℕ)^2141*800000000000^1629 ≤ 254399599397^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091156207 5000000000 254399599397 800000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102635551/2500000000 : ℝ)^2141 ≤ (34100021709651/100000000000000 : ℝ)^1629 := by
    have hnat : (1102635551 : ℕ)^2141*100000000000000^1629 ≤ 34100021709651^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102635551 2500000000 34100021709651 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205271429/5000000000 : ℝ)^2141 ≤ (34100028355279/100000000000000 : ℝ)^1629 := by
    have hnat : (2205271429 : ℕ)^2141*100000000000000^1629 ≤ 34100028355279^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205271429 5000000000 34100028355279 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2091156207/5000000000 : ℝ), (1102635551/2500000000 : ℝ), (2205271429/5000000000 : ℝ)] ![(254399599397/800000000000 : ℝ), (34100021709651/100000000000000 : ℝ), (34100028355279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2091156207/5000000000 : ℝ)|^2141 ≤ (254399599397/800000000000 : ℝ)^1629
        have hw : |(2091156207/5000000000 : ℝ)|=(2091156207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102635551/2500000000 : ℝ)|^2141 ≤ (34100021709651/100000000000000 : ℝ)^1629
        have hw : |(1102635551/2500000000 : ℝ)|=(1102635551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2205271429/5000000000 : ℝ)|^2141 ≤ (34100028355279/100000000000000 : ℝ)^1629
        have hw : |(2205271429/5000000000 : ℝ)|=(2205271429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_8 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2161552331/10000000000 : ℝ)*x 0 + (5177601353/10000000000 : ℝ)*x 1 + (1080960357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161552331/10000000000 : ℝ)^2141 ≤ (13356124737381/100000000000000 : ℝ)^1629 := by
    have hnat : (2161552331 : ℕ)^2141*100000000000000^1629 ≤ 13356124737381^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161552331 10000000000 13356124737381 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177601353/10000000000 : ℝ)^2141 ≤ (21049816059069/50000000000000 : ℝ)^1629 := by
    have hnat : (5177601353 : ℕ)^2141*50000000000000^1629 ≤ 21049816059069^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177601353 10000000000 21049816059069 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080960357/2000000000 : ℝ)^2141 ≤ (8908848625709/20000000000000 : ℝ)^1629 := by
    have hnat : (1080960357 : ℕ)^2141*20000000000000^1629 ≤ 8908848625709^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080960357 2000000000 8908848625709 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2161552331/10000000000 : ℝ), (5177601353/10000000000 : ℝ), (1080960357/2000000000 : ℝ)] ![(13356124737381/100000000000000 : ℝ), (21049816059069/50000000000000 : ℝ), (8908848625709/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2161552331/10000000000 : ℝ)|^2141 ≤ (13356124737381/100000000000000 : ℝ)^1629
        have hw : |(-2161552331/10000000000 : ℝ)|=(2161552331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177601353/10000000000 : ℝ)|^2141 ≤ (21049816059069/50000000000000 : ℝ)^1629
        have hw : |(5177601353/10000000000 : ℝ)|=(5177601353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080960357/2000000000 : ℝ)|^2141 ≤ (8908848625709/20000000000000 : ℝ)^1629
        have hw : |(1080960357/2000000000 : ℝ)|=(1080960357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_9 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275005353/10000000000 : ℝ)*x 0 + (-253969481/1250000000 : ℝ)*x 1 + (5404801463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275005353/10000000000 : ℝ)^2141 ≤ (21571813861949/50000000000000 : ℝ)^1629 := by
    have hnat : (5275005353 : ℕ)^2141*50000000000000^1629 ≤ 21571813861949^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275005353 10000000000 21571813861949 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253969481/1250000000 : ℝ)^2141 ≤ (492485304799/4000000000000 : ℝ)^1629 := by
    have hnat : (253969481 : ℕ)^2141*4000000000000^1629 ≤ 492485304799^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253969481 1250000000 492485304799 4000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404801463/10000000000 : ℝ)^2141 ≤ (44544239640651/100000000000000 : ℝ)^1629 := by
    have hnat : (5404801463 : ℕ)^2141*100000000000000^1629 ≤ 44544239640651^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404801463 10000000000 44544239640651 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275005353/10000000000 : ℝ), (-253969481/1250000000 : ℝ), (5404801463/10000000000 : ℝ)] ![(21571813861949/50000000000000 : ℝ), (492485304799/4000000000000 : ℝ), (44544239640651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275005353/10000000000 : ℝ)|^2141 ≤ (21571813861949/50000000000000 : ℝ)^1629
        have hw : |(5275005353/10000000000 : ℝ)|=(5275005353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253969481/1250000000 : ℝ)|^2141 ≤ (492485304799/4000000000000 : ℝ)^1629
        have hw : |(-253969481/1250000000 : ℝ)|=(253969481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404801463/10000000000 : ℝ)|^2141 ≤ (44544239640651/100000000000000 : ℝ)^1629
        have hw : |(5404801463/10000000000 : ℝ)|=(5404801463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_10 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275005027/10000000000 : ℝ)*x 0 + (1080960357/2000000000 : ℝ)*x 1 + (-2031755851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275005027/10000000000 : ℝ)^2141 ≤ (1348238256861/3125000000000 : ℝ)^1629 := by
    have hnat : (5275005027 : ℕ)^2141*3125000000000^1629 ≤ 1348238256861^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275005027 10000000000 1348238256861 3125000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080960357/2000000000 : ℝ)^2141 ≤ (8908848625709/20000000000000 : ℝ)^1629 := by
    have hnat : (1080960357 : ℕ)^2141*20000000000000^1629 ≤ 8908848625709^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080960357 2000000000 8908848625709 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2031755851/10000000000 : ℝ)^2141 ≤ (12312132643869/100000000000000 : ℝ)^1629 := by
    have hnat : (2031755851 : ℕ)^2141*100000000000000^1629 ≤ 12312132643869^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031755851 10000000000 12312132643869 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275005027/10000000000 : ℝ), (1080960357/2000000000 : ℝ), (-2031755851/10000000000 : ℝ)] ![(1348238256861/3125000000000 : ℝ), (8908848625709/20000000000000 : ℝ), (12312132643869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275005027/10000000000 : ℝ)|^2141 ≤ (1348238256861/3125000000000 : ℝ)^1629
        have hw : |(5275005027/10000000000 : ℝ)|=(5275005027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080960357/2000000000 : ℝ)|^2141 ≤ (8908848625709/20000000000000 : ℝ)^1629
        have hw : |(1080960357/2000000000 : ℝ)|=(1080960357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2031755851/10000000000 : ℝ)|^2141 ≤ (12312132643869/100000000000000 : ℝ)^1629
        have hw : |(-2031755851/10000000000 : ℝ)|=(2031755851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_11 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (180524479/400000000 : ℝ)*x 0 + (530613679/1250000000 : ℝ)*x 1 + (4244909539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180524479/400000000 : ℝ)^2141 ≤ (35146074543739/100000000000000 : ℝ)^1629 := by
    have hnat : (180524479 : ℕ)^2141*100000000000000^1629 ≤ 35146074543739^1629*400000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180524479 400000000 35146074543739 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530613679/1250000000 : ℝ)^2141 ≤ (32426962185867/100000000000000 : ℝ)^1629 := by
    have hnat : (530613679 : ℕ)^2141*100000000000000^1629 ≤ 32426962185867^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530613679 1250000000 32426962185867 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244909539/10000000000 : ℝ)^2141 ≤ (32426963260147/100000000000000 : ℝ)^1629 := by
    have hnat : (4244909539 : ℕ)^2141*100000000000000^1629 ≤ 32426963260147^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244909539 10000000000 32426963260147 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(180524479/400000000 : ℝ), (530613679/1250000000 : ℝ), (4244909539/10000000000 : ℝ)] ![(35146074543739/100000000000000 : ℝ), (32426962185867/100000000000000 : ℝ), (32426963260147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(180524479/400000000 : ℝ)|^2141 ≤ (35146074543739/100000000000000 : ℝ)^1629
        have hw : |(180524479/400000000 : ℝ)|=(180524479/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530613679/1250000000 : ℝ)|^2141 ≤ (32426962185867/100000000000000 : ℝ)^1629
        have hw : |(530613679/1250000000 : ℝ)|=(530613679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244909539/10000000000 : ℝ)|^2141 ≤ (32426963260147/100000000000000 : ℝ)^1629
        have hw : |(4244909539/10000000000 : ℝ)|=(4244909539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_12 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1964339173/10000000000 : ℝ)*x 0 + (5475383343/10000000000 : ℝ)*x 1 + (656676279/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1964339173/10000000000 : ℝ)^2141 ≤ (11778015371759/100000000000000 : ℝ)^1629 := by
    have hnat : (1964339173 : ℕ)^2141*100000000000000^1629 ≤ 11778015371759^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964339173 10000000000 11778015371759 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475383343/10000000000 : ℝ)^2141 ≤ (45310344718493/100000000000000 : ℝ)^1629 := by
    have hnat : (5475383343 : ℕ)^2141*100000000000000^1629 ≤ 45310344718493^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475383343 10000000000 45310344718493 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656676279/1250000000 : ℝ)^2141 ≤ (42911639883587/100000000000000 : ℝ)^1629 := by
    have hnat : (656676279 : ℕ)^2141*100000000000000^1629 ≤ 42911639883587^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656676279 1250000000 42911639883587 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1964339173/10000000000 : ℝ), (5475383343/10000000000 : ℝ), (656676279/1250000000 : ℝ)] ![(11778015371759/100000000000000 : ℝ), (45310344718493/100000000000000 : ℝ), (42911639883587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1964339173/10000000000 : ℝ)|^2141 ≤ (11778015371759/100000000000000 : ℝ)^1629
        have hw : |(-1964339173/10000000000 : ℝ)|=(1964339173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475383343/10000000000 : ℝ)|^2141 ≤ (45310344718493/100000000000000 : ℝ)^1629
        have hw : |(5475383343/10000000000 : ℝ)|=(5475383343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656676279/1250000000 : ℝ)|^2141 ≤ (42911639883587/100000000000000 : ℝ)^1629
        have hw : |(656676279/1250000000 : ℝ)|=(656676279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_13 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5381432563/10000000000 : ℝ)*x 0 + (-2092362327/10000000000 : ℝ)*x 1 + (2626705131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381432563/10000000000 : ℝ)^2141 ≤ (11072820155151/25000000000000 : ℝ)^1629 := by
    have hnat : (5381432563 : ℕ)^2141*25000000000000^1629 ≤ 11072820155151^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381432563 10000000000 11072820155151 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2092362327/10000000000 : ℝ)^2141 ≤ (6398539585191/50000000000000 : ℝ)^1629 := by
    have hnat : (2092362327 : ℕ)^2141*50000000000000^1629 ≤ 6398539585191^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092362327 10000000000 6398539585191 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626705131/5000000000 : ℝ)^2141 ≤ (21455820102829/50000000000000 : ℝ)^1629 := by
    have hnat : (2626705131 : ℕ)^2141*50000000000000^1629 ≤ 21455820102829^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626705131 5000000000 21455820102829 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381432563/10000000000 : ℝ), (-2092362327/10000000000 : ℝ), (2626705131/5000000000 : ℝ)] ![(11072820155151/25000000000000 : ℝ), (6398539585191/50000000000000 : ℝ), (21455820102829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381432563/10000000000 : ℝ)|^2141 ≤ (11072820155151/25000000000000 : ℝ)^1629
        have hw : |(5381432563/10000000000 : ℝ)|=(5381432563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2092362327/10000000000 : ℝ)|^2141 ≤ (6398539585191/50000000000000 : ℝ)^1629
        have hw : |(-2092362327/10000000000 : ℝ)|=(2092362327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626705131/5000000000 : ℝ)|^2141 ≤ (21455820102829/50000000000000 : ℝ)^1629
        have hw : |(2626705131/5000000000 : ℝ)|=(2626705131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_14 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1076286541/2000000000 : ℝ)*x 0 + (2626705049/5000000000 : ℝ)*x 1 + (-2092362353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076286541/2000000000 : ℝ)^2141 ≤ (44291282156651/100000000000000 : ℝ)^1629 := by
    have hnat : (1076286541 : ℕ)^2141*100000000000000^1629 ≤ 44291282156651^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076286541 2000000000 44291282156651 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626705049/5000000000 : ℝ)^2141 ≤ (42911638445007/100000000000000 : ℝ)^1629 := by
    have hnat : (2626705049 : ℕ)^2141*100000000000000^1629 ≤ 42911638445007^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626705049 5000000000 42911638445007 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2092362353/10000000000 : ℝ)^2141 ≤ (639853968969/5000000000000 : ℝ)^1629 := by
    have hnat : (2092362353 : ℕ)^2141*5000000000000^1629 ≤ 639853968969^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092362353 10000000000 639853968969 5000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076286541/2000000000 : ℝ), (2626705049/5000000000 : ℝ), (-2092362353/10000000000 : ℝ)] ![(44291282156651/100000000000000 : ℝ), (42911638445007/100000000000000 : ℝ), (639853968969/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076286541/2000000000 : ℝ)|^2141 ≤ (44291282156651/100000000000000 : ℝ)^1629
        have hw : |(1076286541/2000000000 : ℝ)|=(1076286541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626705049/5000000000 : ℝ)|^2141 ≤ (42911638445007/100000000000000 : ℝ)^1629
        have hw : |(2626705049/5000000000 : ℝ)|=(2626705049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2092362353/10000000000 : ℝ)|^2141 ≤ (639853968969/5000000000000 : ℝ)^1629
        have hw : |(-2092362353/10000000000 : ℝ)|=(2092362353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_box_15 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4155769113/10000000000 : ℝ)*x 0 + (4423575517/10000000000 : ℝ)*x 1 + (1105893771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4155769113/10000000000 : ℝ)^2141 ≤ (31534961758289/100000000000000 : ℝ)^1629 := by
    have hnat : (4155769113 : ℕ)^2141*100000000000000^1629 ≤ 31534961758289^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155769113 10000000000 31534961758289 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4423575517/10000000000 : ℝ)^2141 ≤ (21395325821/62500000000 : ℝ)^1629 := by
    have hnat : (4423575517 : ℕ)^2141*62500000000^1629 ≤ 21395325821^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4423575517 10000000000 21395325821 62500000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105893771/2500000000 : ℝ)^2141 ≤ (2139532306849/6250000000000 : ℝ)^1629 := by
    have hnat : (1105893771 : ℕ)^2141*6250000000000^1629 ≤ 2139532306849^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105893771 2500000000 2139532306849 6250000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4155769113/10000000000 : ℝ), (4423575517/10000000000 : ℝ), (1105893771/2500000000 : ℝ)] ![(31534961758289/100000000000000 : ℝ), (21395325821/62500000000 : ℝ), (2139532306849/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4155769113/10000000000 : ℝ)|^2141 ≤ (31534961758289/100000000000000 : ℝ)^1629
        have hw : |(4155769113/10000000000 : ℝ)|=(4155769113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4423575517/10000000000 : ℝ)|^2141 ≤ (21395325821/62500000000 : ℝ)^1629
        have hw : |(4423575517/10000000000 : ℝ)|=(4423575517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105893771/2500000000 : ℝ)|^2141 ≤ (2139532306849/6250000000000 : ℝ)^1629
        have hw : |(1105893771/2500000000 : ℝ)|=(1105893771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1322_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1964/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29451/50000 : ℝ) ∧ (79837/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42137/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5551/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5551/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5551/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5551/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5551/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5551/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5551/50000 : ℝ) ^ (4281/1024 : ℝ) ≤ (1276595213907843/12500000000000000000 : ℝ) := by
    have hpowers : (5551/50000 : ℝ)^4281 ≤ (1276595213907843/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5551 : ℕ)^4281*12500000000000000000^1024 ≤ 1276595213907843^1024*50000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5551 50000 1276595213907843 12500000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5551/50000 : ℝ)) (X := (1276595213907843/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14693/100000 : ℝ) ^ (4281/1024 : ℝ) ≤ (32958596522514863/100000000000000000000 : ℝ) := by
    have hpowers : (14693/100000 : ℝ)^4281 ≤ (32958596522514863/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14693 : ℕ)^4281*100000000000000000000^1024 ≤ 32958596522514863^1024*100000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14693 100000 32958596522514863 100000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14693/100000 : ℝ)) (X := (32958596522514863/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251276595213907843/6250000000000000000 : ℝ) ≤ (10000488533311063/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (6251276595213907843/6250000000000000000 : ℝ)^1024 ≤ (10000488533311063/10000000000000000 : ℝ)^4281 := by
      have hnat : (6251276595213907843 : ℕ)^1024*10000000000000000^4281 ≤ 10000488533311063^4281*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251276595213907843 6250000000000000000 10000488533311063 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000488533311063/10000000000000000 : ℝ)) (X := (6251276595213907843/6250000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043171358233777607/100000000000000000000 : ℝ) ≤ (5000516237009059/5000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (100043171358233777607/100000000000000000000 : ℝ)^1024 ≤ (5000516237009059/5000000000000000 : ℝ)^4281 := by
      have hnat : (100043171358233777607 : ℕ)^1024*5000000000000000^4281 ≤ 5000516237009059^4281*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043171358233777607 100000000000000000000 5000516237009059 5000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000516237009059/5000000000000000 : ℝ)) (X := (100043171358233777607/100000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032958596522514863/50000000000000000000 : ℝ) ≤ (10001576414725173/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (50032958596522514863/50000000000000000000 : ℝ)^1024 ≤ (10001576414725173/10000000000000000 : ℝ)^4281 := by
      have hnat : (50032958596522514863 : ℕ)^1024*10000000000000000^4281 ≤ 10001576414725173^4281*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032958596522514863 50000000000000000000 10001576414725173 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001576414725173/10000000000000000 : ℝ)) (X := (50032958596522514863/50000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1276595213907843/12500000000000000000 : ℝ) ≤ ((5128525237665796859/5130000000000000000 : ℝ)+2*(108788141411/71820000000000 : ℝ)*(5551/50000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (5128525237665796859/5130000000000000000 : ℝ)+2*(108788141411/71820000000000 : ℝ)*(5551/50000 : ℝ)=(10000488533311063/10000000000000000 : ℝ) by norm_num, show 1+2*(1276595213907843/12500000000000000000 : ℝ)=(6251276595213907843/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32958596522514863/100000000000000000000 : ℝ)+(1276595213907843/12500000000000000000 : ℝ) ≤ ((5128525237665796859/5130000000000000000 : ℝ)+(108788141411/71820000000000 : ℝ)*((14693/100000 : ℝ)+(5551/50000 : ℝ)))^(4281/1024 : ℝ) := by
    rw [show (5128525237665796859/5130000000000000000 : ℝ)+(108788141411/71820000000000 : ℝ)*((14693/100000 : ℝ)+(5551/50000 : ℝ))=(5000516237009059/5000000000000000 : ℝ) by norm_num, show 1+(32958596522514863/100000000000000000000 : ℝ)+(1276595213907843/12500000000000000000 : ℝ)=(100043171358233777607/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32958596522514863/100000000000000000000 : ℝ) ≤ ((5128525237665796859/5130000000000000000 : ℝ)+2*(108788141411/71820000000000 : ℝ)*(14693/100000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (5128525237665796859/5130000000000000000 : ℝ)+2*(108788141411/71820000000000 : ℝ)*(14693/100000 : ℝ)=(10001576414725173/10000000000000000 : ℝ) by norm_num, show 1+2*(32958596522514863/100000000000000000000 : ℝ)=(50032958596522514863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5128525237665796859/5130000000000000000 : ℝ)*(X 1 0+X 2 0)+(108788141411/71820000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (5551/50000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (5128525237665796859/5130000000000000000 : ℝ)) (alpha := (108788141411/71820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5128525237665796859/5130000000000000000 : ℝ)*(X 0 1+X 2 1)+(108788141411/71820000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (5551/50000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (5128525237665796859/5130000000000000000 : ℝ)) (alpha := (108788141411/71820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5128525237665796859/5130000000000000000 : ℝ)*(X 0 2+X 1 2)+(108788141411/71820000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (5551/50000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (5128525237665796859/5130000000000000000 : ℝ)) (alpha := (108788141411/71820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1892515663/10000000000 : ℝ)*X 0 0+(5390773821/10000000000 : ℝ)*X 0 1+(1078154713/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((41288059/78125000 : ℝ)*X 1 0+(-1018751443/5000000000 : ℝ)*X 1 1+(2695387111/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5284871937/10000000000 : ℝ)*X 2 0+(5390773941/10000000000 : ℝ)*X 2 1+(-2037502749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((224027481/500000000 : ℝ)*X 0 0+(133171197/312500000 : ℝ)*X 0 1+(4261478117/10000000000 : ℝ)*X 0 2+(224027481/500000000 : ℝ)*X 1 0+(133171197/312500000 : ℝ)*X 1 1+(4261478117/10000000000 : ℝ)*X 1 2+(224027481/500000000 : ℝ)*X 2 0+(133171197/312500000 : ℝ)*X 2 1+(4261478117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1116499551/5000000000 : ℝ)*X 0 0+(5264462547/10000000000 : ℝ)*X 0 1+(2632231143/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1074733249/2000000000 : ℝ)*X 1 0+(-20880447/100000000 : ℝ)*X 1 1+(2632230973/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5373666277/10000000000 : ℝ)*X 2 0+(1316115577/2500000000 : ℝ)*X 2 1+(-522011043/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2091156207/5000000000 : ℝ)*X 0 0+(1102635551/2500000000 : ℝ)*X 0 1+(2205271429/5000000000 : ℝ)*X 0 2+(2091156207/5000000000 : ℝ)*X 1 0+(1102635551/2500000000 : ℝ)*X 1 1+(2205271429/5000000000 : ℝ)*X 1 2+(2091156207/5000000000 : ℝ)*X 2 0+(1102635551/2500000000 : ℝ)*X 2 1+(2205271429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2161552331/10000000000 : ℝ)*X 0 0+(5177601353/10000000000 : ℝ)*X 0 1+(1080960357/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275005353/10000000000 : ℝ)*X 1 0+(-253969481/1250000000 : ℝ)*X 1 1+(5404801463/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275005027/10000000000 : ℝ)*X 2 0+(1080960357/2000000000 : ℝ)*X 2 1+(-2031755851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((180524479/400000000 : ℝ)*X 0 0+(530613679/1250000000 : ℝ)*X 0 1+(4244909539/10000000000 : ℝ)*X 0 2+(180524479/400000000 : ℝ)*X 1 0+(530613679/1250000000 : ℝ)*X 1 1+(4244909539/10000000000 : ℝ)*X 1 2+(180524479/400000000 : ℝ)*X 2 0+(530613679/1250000000 : ℝ)*X 2 1+(4244909539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1964339173/10000000000 : ℝ)*X 0 0+(5475383343/10000000000 : ℝ)*X 0 1+(656676279/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5381432563/10000000000 : ℝ)*X 1 0+(-2092362327/10000000000 : ℝ)*X 1 1+(2626705131/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1076286541/2000000000 : ℝ)*X 2 0+(2626705049/5000000000 : ℝ)*X 2 1+(-2092362353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4155769113/10000000000 : ℝ)*X 0 0+(4423575517/10000000000 : ℝ)*X 0 1+(1105893771/2500000000 : ℝ)*X 0 2+(4155769113/10000000000 : ℝ)*X 1 0+(4423575517/10000000000 : ℝ)*X 1 1+(1105893771/2500000000 : ℝ)*X 1 2+(4155769113/10000000000 : ℝ)*X 2 0+(4423575517/10000000000 : ℝ)*X 2 1+(1105893771/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1964/3125 : ℝ) ≤ (-2828048702588169568889478064327/4500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94788083/50000000000000 : ℝ)*(upper0) + (177021847/100000000000000 : ℝ)*(lower2) + (762049/1562500000000 : ℝ)*(lower3) + (2898101855376193/100000000000000 : ℝ)*(major0) + (2898101855376193/100000000000000 : ℝ)*(major1) + (2898101855376193/100000000000000 : ℝ)*(major2) + (4670691073/50000000000000 : ℝ)*(sp1) + (22798267/2500000000000 : ℝ)*(sp3) + (98363635360187/2500000000000 : ℝ)*(sp4) + (1967269211863729/50000000000000 : ℝ)*(sp5) + (1967221422930677/50000000000000 : ℝ)*(sp6) + (1882603542620151/100000000000000 : ℝ)*(sp7) + (587675531/25000000000000 : ℝ)*(sp8) + (104919248251/100000000000000 : ℝ)*(sp14) + (1882604454550831/100000000000000 : ℝ)*(f.failure) + (983636941277401/25000000000000 : ℝ)*(f.sum) + (1237145126773/189000000000000000000000000 : ℝ)*base66 + (31834838679561079/21000000000000000000000000000000 : ℝ)*base67 + (331005842438921/21000000000000000000000000000000 : ℝ)*base70 + (139038319580438921/21000000000000000000000000000000 : ℝ)*base72 + (1618386101533/37800000000000000000000000 : ℝ)*base73 + (28247630102438921/21000000000000000000000000000000 : ℝ)*base76 + (371349606011438921/21000000000000000000000000000000 : ℝ)*base78 + (495513614421561079/21000000000000000000000000000000 : ℝ)*base79 + (173868950257/94500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1588137/2500000000000000000000 : ℝ)*base90 + (1588137/2500000000000000000000 : ℝ)*base92 + (1588137/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29451/50000 : ℝ) ≤ (2350307776880401693402942117723/3990000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21889811/50000000000000 : ℝ)*(upper0) + (4903679/25000000000000 : ℝ)*(upper3) + (143634741/100000000000000 : ℝ)*(upper4) + (59322674597671/2000000000000 : ℝ)*(major0) + (59322674597671/2000000000000 : ℝ)*(major1) + (59322674597671/2000000000000 : ℝ)*(major2) + (1992914278615029/50000000000000 : ℝ)*(sp0) + (797163212388291/20000000000000 : ℝ)*(sp1) + (1992908583890913/50000000000000 : ℝ)*(sp2) + (12042465174277/625000000000 : ℝ)*(sp3) + (3702185587/20000000000000 : ℝ)*(sp5) + (4351271891/25000000000000 : ℝ)*(sp6) + (434176087/12500000000000 : ℝ)*(sp7) + (1503909833/25000000000000 : ℝ)*(sp8) + (385359580258603/20000000000000 : ℝ)*(f.failure) + (398583457286939/10000000000000 : ℝ)*(f.sum) + (1927016145121/448875000000000000000000000 : ℝ)*base66 + (79323964418650253/7980000000000000000000000000000 : ℝ)*base68 + (41004929460250253/7980000000000000000000000000000 : ℝ)*base70 + (25955525512630253/7980000000000000000000000000000 : ℝ)*base72 + (24779809525661/897750000000000000000000000 : ℝ)*base74 + (73271342297650253/7980000000000000000000000000000 : ℝ)*base76 + (28420180073530253/7980000000000000000000000000000 : ℝ)*base78 + (231165857607370253/7980000000000000000000000000000 : ℝ)*base80 + (317391276701/224437500000000000000000000 : ℝ)*base82 + (2946381/500000000000000000000 : ℝ)*base90 + (2946381/500000000000000000000 : ℝ)*base92 + (2946381/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79837/100000 : ℝ) ≤ (39819699611377057349981142109403/49875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34325693/50000000000000 : ℝ)*(upper2) + (15753081/100000000000000 : ℝ)*(lower3) + (7573997/20000000000000 : ℝ)*(lower5) + (819760773082031/25000000000000 : ℝ)*(major0) + (819760773082031/25000000000000 : ℝ)*(major1) + (819760773082031/25000000000000 : ℝ)*(major2) + (7584397533/10000000000000 : ℝ)*(sp2) + (11919591281/25000000000000 : ℝ)*(sp3) + (5248258999/100000000000000 : ℝ)*(sp4) + (1100350232399133/25000000000000 : ℝ)*(sp8) + (2200704816847979/50000000000000 : ℝ)*(sp9) + (1100333447430157/25000000000000 : ℝ)*(sp10) + (2130015873690311/100000000000000 : ℝ)*(sp11) + (3455840427/100000000000000 : ℝ)*(sp12) + (1065031776027717/50000000000000 : ℝ)*(f.failure) + (2200704816847979/50000000000000 : ℝ)*(f.sum) + (202775780353/44887500000000000000000000 : ℝ)*base66 + (795667013300001733/99750000000000000000000000000000 : ℝ)*base68 + (1200744758555751733/99750000000000000000000000000000 : ℝ)*base70 + (807196270019751733/99750000000000000000000000000000 : ℝ)*base72 + (396230478073/179550000000000000000000000 : ℝ)*base74 + (767382495116751733/99750000000000000000000000000000 : ℝ)*base76 + (611531457221751733/99750000000000000000000000000000 : ℝ)*base78 + (456145025600001733/99750000000000000000000000000000 : ℝ)*base80 + (4165752694717/718200000000000000000000000 : ℝ)*base82 + (5688259/1250000000000000000000 : ℝ)*base90 + (5688259/1250000000000000000000 : ℝ)*base92 + (5688259/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-42137/50000 : ℝ) ≤ (-252181686535449799881024232859041/299250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117461877/100000000000000 : ℝ)*(upper1) + (35541867/25000000000000 : ℝ)*(upper3) + (190241957/100000000000000 : ℝ)*(upper5) + (1657641786734281/50000000000000 : ℝ)*(major0) + (1657641786734281/50000000000000 : ℝ)*(major1) + (1657641786734281/50000000000000 : ℝ)*(major2) + (1748872121/20000000000000 : ℝ)*(sp4) + (9435098463/50000000000000 : ℝ)*(sp5) + (25309877451/25000000000000 : ℝ)*(sp6) + (33348017199/50000000000000 : ℝ)*(sp7) + (4505043478794717/100000000000000 : ℝ)*(sp12) + (1126258338239599/25000000000000 : ℝ)*(sp13) + (2252475491822759/50000000000000 : ℝ)*(sp14) + (2153538641173787/100000000000000 : ℝ)*(sp15) + (430721067441637/20000000000000 : ℝ)*(f.failure) + (2252526111577661/50000000000000 : ℝ)*(f.sum) + (183298811627/71820000000000000000000000 : ℝ)*base65 + (157471108948448483/199500000000000000000000000000000 : ℝ)*base68 + (8686011127733948483/199500000000000000000000000000000 : ℝ)*base70 + (1122473273956448483/199500000000000000000000000000000 : ℝ)*base72 + (18134683246007/3591000000000000000000000000 : ℝ)*base74 + (1611072877346948483/199500000000000000000000000000000 : ℝ)*base76 + (1539415122916448483/199500000000000000000000000000000 : ℝ)*base78 + (357998240683448483/199500000000000000000000000000000 : ℝ)*base80 + (13121434469879/448875000000000000000000000 : ℝ)*base81 + (1511901/500000000000000000000 : ℝ)*base89 + (1511901/500000000000000000000 : ℝ)*base91 + (1511901/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1322_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1964/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(29451/50000 : ℝ) else (79837/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42137/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1322_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1322_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1964/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(29451/50000 : ℝ) else (79837/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42137/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1322_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1322_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1322_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1964/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(29451/50000 : ℝ) else (79837/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42137/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1322_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
