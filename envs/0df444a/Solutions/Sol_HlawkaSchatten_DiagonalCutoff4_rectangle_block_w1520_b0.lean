-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1520_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:57:10.952502+00:00
-- url     : https://prove2.me/submissions/b3e58705-eb44-450a-bffc-10fc2e875a40

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
theorem support_rectangle_w1520_s0_0 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1677382081/10000000000 : ℝ)*x 0 + (295334769/500000000 : ℝ)*x 1 + (971744851/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1677382081/10000000000 : ℝ)^4537 ≤ (1993659290601/20000000000000 : ℝ)^3513 := by
    have hnat : (1677382081 : ℕ)^4537*20000000000000^3513 ≤ 1993659290601^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677382081 10000000000 1993659290601 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295334769/500000000 : ℝ)^4537 ≤ (50663371601497/100000000000000 : ℝ)^3513 := by
    have hnat : (295334769 : ℕ)^4537*100000000000000^3513 ≤ 50663371601497^3513*500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295334769 500000000 50663371601497 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971744851/2000000000 : ℝ)^4537 ≤ (2460520745667/6250000000000 : ℝ)^3513 := by
    have hnat : (971744851 : ℕ)^4537*6250000000000^3513 ≤ 2460520745667^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971744851 2000000000 2460520745667 6250000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1677382081/10000000000 : ℝ), (295334769/500000000 : ℝ), (971744851/2000000000 : ℝ)] ![(1993659290601/20000000000000 : ℝ), (50663371601497/100000000000000 : ℝ), (2460520745667/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1677382081/10000000000 : ℝ)|^4537 ≤ (1993659290601/20000000000000 : ℝ)^3513
        have hw : |(-1677382081/10000000000 : ℝ)|=(1677382081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(295334769/500000000 : ℝ)|^4537 ≤ (50663371601497/100000000000000 : ℝ)^3513
        have hw : |(295334769/500000000 : ℝ)|=(295334769/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(971744851/2000000000 : ℝ)|^4537 ≤ (2460520745667/6250000000000 : ℝ)^3513
        have hw : |(971744851/2000000000 : ℝ)|=(971744851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s0_1 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5476241311/10000000000 : ℝ)*x 0 + (-1132093701/5000000000 : ℝ)*x 1 + (1214681049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5476241311/10000000000 : ℝ)^4537 ≤ (22973289909273/50000000000000 : ℝ)^3513 := by
    have hnat : (5476241311 : ℕ)^4537*50000000000000^3513 ≤ 22973289909273^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476241311 10000000000 22973289909273 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132093701/5000000000 : ℝ)^4537 ≤ (3671272214361/25000000000000 : ℝ)^3513 := by
    have hnat : (1132093701 : ℕ)^4537*25000000000000^3513 ≤ 3671272214361^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132093701 5000000000 3671272214361 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1214681049/2500000000 : ℝ)^4537 ≤ (39368331313271/100000000000000 : ℝ)^3513 := by
    have hnat : (1214681049 : ℕ)^4537*100000000000000^3513 ≤ 39368331313271^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214681049 2500000000 39368331313271 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5476241311/10000000000 : ℝ), (-1132093701/5000000000 : ℝ), (1214681049/2500000000 : ℝ)] ![(22973289909273/50000000000000 : ℝ), (3671272214361/25000000000000 : ℝ), (39368331313271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5476241311/10000000000 : ℝ)|^4537 ≤ (22973289909273/50000000000000 : ℝ)^3513
        have hw : |(5476241311/10000000000 : ℝ)|=(5476241311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1132093701/5000000000 : ℝ)|^4537 ≤ (3671272214361/25000000000000 : ℝ)^3513
        have hw : |(-1132093701/5000000000 : ℝ)|=(1132093701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1214681049/2500000000 : ℝ)|^4537 ≤ (39368331313271/100000000000000 : ℝ)^3513
        have hw : |(1214681049/2500000000 : ℝ)|=(1214681049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s0_2 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5476241381/10000000000 : ℝ)*x 0 + (485872423/1000000000 : ℝ)*x 1 + (-566046817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5476241381/10000000000 : ℝ)^4537 ≤ (11486645144263/25000000000000 : ℝ)^3513 := by
    have hnat : (5476241381 : ℕ)^4537*25000000000000^3513 ≤ 11486645144263^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476241381 10000000000 11486645144263 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (485872423/1000000000 : ℝ)^4537 ≤ (19684165834531/50000000000000 : ℝ)^3513 := by
    have hnat : (485872423 : ℕ)^4537*50000000000000^3513 ≤ 19684165834531^3513*1000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485872423 1000000000 19684165834531 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566046817/2500000000 : ℝ)^4537 ≤ (7342543867507/50000000000000 : ℝ)^3513 := by
    have hnat : (566046817 : ℕ)^4537*50000000000000^3513 ≤ 7342543867507^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566046817 2500000000 7342543867507 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5476241381/10000000000 : ℝ), (485872423/1000000000 : ℝ), (-566046817/2500000000 : ℝ)] ![(11486645144263/25000000000000 : ℝ), (19684165834531/50000000000000 : ℝ), (7342543867507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5476241381/10000000000 : ℝ)|^4537 ≤ (11486645144263/25000000000000 : ℝ)^3513
        have hw : |(5476241381/10000000000 : ℝ)|=(5476241381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(485872423/1000000000 : ℝ)|^4537 ≤ (19684165834531/50000000000000 : ℝ)^3513
        have hw : |(485872423/1000000000 : ℝ)|=(485872423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-566046817/2500000000 : ℝ)|^4537 ≤ (7342543867507/50000000000000 : ℝ)^3513
        have hw : |(-566046817/2500000000 : ℝ)|=(566046817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s0_3 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4142993549/10000000000 : ℝ)*x 0 + (24151273/78125000 : ℝ)*x 1 + (5481129217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4142993549/10000000000 : ℝ)^4537 ≤ (16022698854633/50000000000000 : ℝ)^3513 := by
    have hnat : (4142993549 : ℕ)^4537*50000000000000^3513 ≤ 16022698854633^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142993549 10000000000 16022698854633 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24151273/78125000 : ℝ)^4537 ≤ (21955051164951/100000000000000 : ℝ)^3513 := by
    have hnat : (24151273 : ℕ)^4537*100000000000000^3513 ≤ 21955051164951^3513*78125000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24151273 78125000 21955051164951 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5481129217/10000000000 : ℝ)^4537 ≤ (45999551110671/100000000000000 : ℝ)^3513 := by
    have hnat : (5481129217 : ℕ)^4537*100000000000000^3513 ≤ 45999551110671^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481129217 10000000000 45999551110671 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4142993549/10000000000 : ℝ), (24151273/78125000 : ℝ), (5481129217/10000000000 : ℝ)] ![(16022698854633/50000000000000 : ℝ), (21955051164951/100000000000000 : ℝ), (45999551110671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4142993549/10000000000 : ℝ)|^4537 ≤ (16022698854633/50000000000000 : ℝ)^3513
        have hw : |(4142993549/10000000000 : ℝ)|=(4142993549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(24151273/78125000 : ℝ)|^4537 ≤ (21955051164951/100000000000000 : ℝ)^3513
        have hw : |(24151273/78125000 : ℝ)|=(24151273/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5481129217/10000000000 : ℝ)|^4537 ≤ (45999551110671/100000000000000 : ℝ)^3513
        have hw : |(5481129217/10000000000 : ℝ)|=(5481129217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s0_4 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-336166937/2000000000 : ℝ)*x 0 + (122135351/250000000 : ℝ)*x 1 + (1469762683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336166937/2000000000 : ℝ)^4537 ≤ (4997401603453/50000000000000 : ℝ)^3513 := by
    have hnat : (336166937 : ℕ)^4537*50000000000000^3513 ≤ 4997401603453^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336166937 2000000000 4997401603453 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122135351/250000000 : ℝ)^4537 ≤ (39647848509937/100000000000000 : ℝ)^3513 := by
    have hnat : (122135351 : ℕ)^4537*100000000000000^3513 ≤ 39647848509937^3513*250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122135351 250000000 39647848509937 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1469762683/2500000000 : ℝ)^4537 ≤ (25178674134717/50000000000000 : ℝ)^3513 := by
    have hnat : (1469762683 : ℕ)^4537*50000000000000^3513 ≤ 25178674134717^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469762683 2500000000 25178674134717 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-336166937/2000000000 : ℝ), (122135351/250000000 : ℝ), (1469762683/2500000000 : ℝ)] ![(4997401603453/50000000000000 : ℝ), (39647848509937/100000000000000 : ℝ), (25178674134717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-336166937/2000000000 : ℝ)|^4537 ≤ (4997401603453/50000000000000 : ℝ)^3513
        have hw : |(-336166937/2000000000 : ℝ)|=(336166937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(122135351/250000000 : ℝ)|^4537 ≤ (39647848509937/100000000000000 : ℝ)^3513
        have hw : |(122135351/250000000 : ℝ)|=(122135351/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1469762683/2500000000 : ℝ)|^4537 ≤ (25178674134717/50000000000000 : ℝ)^3513
        have hw : |(1469762683/2500000000 : ℝ)|=(1469762683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s0_5 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (25949447/50000000 : ℝ)*x 0 + (-310965241/2500000000 : ℝ)*x 1 + (2939525389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25949447/50000000 : ℝ)^4537 ≤ (21433835679211/50000000000000 : ℝ)^3513 := by
    have hnat : (25949447 : ℕ)^4537*50000000000000^3513 ≤ 21433835679211^3513*50000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25949447 50000000 21433835679211 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310965241/2500000000 : ℝ)^4537 ≤ (846872481279/12500000000000 : ℝ)^3513 := by
    have hnat : (310965241 : ℕ)^4537*12500000000000^3513 ≤ 846872481279^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310965241 2500000000 846872481279 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2939525389/5000000000 : ℝ)^4537 ≤ (50357348778301/100000000000000 : ℝ)^3513 := by
    have hnat : (2939525389 : ℕ)^4537*100000000000000^3513 ≤ 50357348778301^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2939525389 5000000000 50357348778301 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(25949447/50000000 : ℝ), (-310965241/2500000000 : ℝ), (2939525389/5000000000 : ℝ)] ![(21433835679211/50000000000000 : ℝ), (846872481279/12500000000000 : ℝ), (50357348778301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(25949447/50000000 : ℝ)|^4537 ≤ (21433835679211/50000000000000 : ℝ)^3513
        have hw : |(25949447/50000000 : ℝ)|=(25949447/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-310965241/2500000000 : ℝ)|^4537 ≤ (846872481279/12500000000000 : ℝ)^3513
        have hw : |(-310965241/2500000000 : ℝ)|=(310965241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2939525389/5000000000 : ℝ)|^4537 ≤ (50357348778301/100000000000000 : ℝ)^3513
        have hw : |(2939525389/5000000000 : ℝ)|=(2939525389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s0_6 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5189889359/10000000000 : ℝ)*x 0 + (2939525467/5000000000 : ℝ)*x 1 + (-621930391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5189889359/10000000000 : ℝ)^4537 ≤ (8573534184211/20000000000000 : ℝ)^3513 := by
    have hnat : (5189889359 : ℕ)^4537*20000000000000^3513 ≤ 8573534184211^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189889359 10000000000 8573534184211 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2939525467/5000000000 : ℝ)^4537 ≤ (50357350504023/100000000000000 : ℝ)^3513 := by
    have hnat : (2939525467 : ℕ)^4537*100000000000000^3513 ≤ 50357350504023^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2939525467 5000000000 50357350504023 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (621930391/5000000000 : ℝ)^4537 ≤ (1693744642493/25000000000000 : ℝ)^3513 := by
    have hnat : (621930391 : ℕ)^4537*25000000000000^3513 ≤ 1693744642493^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621930391 5000000000 1693744642493 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5189889359/10000000000 : ℝ), (2939525467/5000000000 : ℝ), (-621930391/5000000000 : ℝ)] ![(8573534184211/20000000000000 : ℝ), (50357350504023/100000000000000 : ℝ), (1693744642493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5189889359/10000000000 : ℝ)|^4537 ≤ (8573534184211/20000000000000 : ℝ)^3513
        have hw : |(5189889359/10000000000 : ℝ)|=(5189889359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2939525467/5000000000 : ℝ)|^4537 ≤ (50357350504023/100000000000000 : ℝ)^3513
        have hw : |(2939525467/5000000000 : ℝ)|=(2939525467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-621930391/5000000000 : ℝ)|^4537 ≤ (1693744642493/25000000000000 : ℝ)^3513
        have hw : |(-621930391/5000000000 : ℝ)|=(621930391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s0_7 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4150866513/10000000000 : ℝ)*x 0 + (1355066617/2500000000 : ℝ)*x 1 + (157720157/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4150866513/10000000000 : ℝ)^4537 ≤ (32124066145101/100000000000000 : ℝ)^3513 := by
    have hnat : (4150866513 : ℕ)^4537*100000000000000^3513 ≤ 32124066145101^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150866513 10000000000 32124066145101 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355066617/2500000000 : ℝ)^4537 ≤ (1416904781247/3125000000000 : ℝ)^3513 := by
    have hnat : (1355066617 : ℕ)^4537*3125000000000^3513 ≤ 1416904781247^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355066617 2500000000 1416904781247 3125000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157720157/500000000 : ℝ)^4537 ≤ (22534980846013/100000000000000 : ℝ)^3513 := by
    have hnat : (157720157 : ℕ)^4537*100000000000000^3513 ≤ 22534980846013^3513*500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157720157 500000000 22534980846013 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4150866513/10000000000 : ℝ), (1355066617/2500000000 : ℝ), (157720157/500000000 : ℝ)] ![(32124066145101/100000000000000 : ℝ), (1416904781247/3125000000000 : ℝ), (22534980846013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4150866513/10000000000 : ℝ)|^4537 ≤ (32124066145101/100000000000000 : ℝ)^3513
        have hw : |(4150866513/10000000000 : ℝ)|=(4150866513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355066617/2500000000 : ℝ)|^4537 ≤ (1416904781247/3125000000000 : ℝ)^3513
        have hw : |(1355066617/2500000000 : ℝ)|=(1355066617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157720157/500000000 : ℝ)|^4537 ≤ (22534980846013/100000000000000 : ℝ)^3513
        have hw : |(157720157/500000000 : ℝ)|=(157720157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1520_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (293/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25381/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4535/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4535 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4535*1^1024 ≤ 0^1024*1^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4535/1024 : ℝ) ≤ (432094501446466469/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4535 ≤ (432094501446466469/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4535*25000000000000000000^1024 ≤ 432094501446466469^1024*5^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 432094501446466469 25000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (432094501446466469/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4535 := by
      have hnat : (1 : ℕ)^1024*1^4535 ≤ 1^4535*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25432094501446466469/25000000000000000000 : ℝ) ≤ (200775363766499/200000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (25432094501446466469/25000000000000000000 : ℝ)^1024 ≤ (200775363766499/200000000000000 : ℝ)^4535 := by
      have hnat : (25432094501446466469 : ℕ)^1024*200000000000000^4535 ≤ 200775363766499^4535*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25432094501446466469 25000000000000000000 200775363766499 200000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200775363766499/200000000000000 : ℝ)) (X := (25432094501446466469/25000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12932094501446466469/12500000000000000000 : ℝ) ≤ (100775363766499/100000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (12932094501446466469/12500000000000000000 : ℝ)^1024 ≤ (100775363766499/100000000000000 : ℝ)^4535 := by
      have hnat : (12932094501446466469 : ℕ)^1024*100000000000000^4535 ≤ 100775363766499^4535*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12932094501446466469 12500000000000000000 100775363766499 100000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100775363766499/100000000000000 : ℝ)) (X := (12932094501446466469/12500000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(775363766499/80000000000000 : ℝ)*(0 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(775363766499/80000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(432094501446466469/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(775363766499/80000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4535/1024 : ℝ) := by
    rw [show (1 : ℝ)+(775363766499/80000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(200775363766499/200000000000000 : ℝ) by norm_num, show 1+(432094501446466469/25000000000000000000 : ℝ)+(0 : ℝ)=(25432094501446466469/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(432094501446466469/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(775363766499/80000000000000 : ℝ)*(2/5 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(775363766499/80000000000000 : ℝ)*(2/5 : ℝ)=(100775363766499/100000000000000 : ℝ) by norm_num, show 1+2*(432094501446466469/25000000000000000000 : ℝ)=(12932094501446466469/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(775363766499/80000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (775363766499/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(775363766499/80000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (775363766499/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(775363766499/80000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (775363766499/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1677382081/10000000000 : ℝ)*X 0 0+(295334769/500000000 : ℝ)*X 0 1+(971744851/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5476241311/10000000000 : ℝ)*X 1 0+(-1132093701/5000000000 : ℝ)*X 1 1+(1214681049/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5476241381/10000000000 : ℝ)*X 2 0+(485872423/1000000000 : ℝ)*X 2 1+(-566046817/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4142993549/10000000000 : ℝ)*X 0 0+(24151273/78125000 : ℝ)*X 0 1+(5481129217/10000000000 : ℝ)*X 0 2+(4142993549/10000000000 : ℝ)*X 1 0+(24151273/78125000 : ℝ)*X 1 1+(5481129217/10000000000 : ℝ)*X 1 2+(4142993549/10000000000 : ℝ)*X 2 0+(24151273/78125000 : ℝ)*X 2 1+(5481129217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-336166937/2000000000 : ℝ)*X 0 0+(122135351/250000000 : ℝ)*X 0 1+(1469762683/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((25949447/50000000 : ℝ)*X 1 0+(-310965241/2500000000 : ℝ)*X 1 1+(2939525389/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5189889359/10000000000 : ℝ)*X 2 0+(2939525467/5000000000 : ℝ)*X 2 1+(-621930391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4150866513/10000000000 : ℝ)*X 0 0+(1355066617/2500000000 : ℝ)*X 0 1+(157720157/500000000 : ℝ)*X 0 2+(4150866513/10000000000 : ℝ)*X 1 0+(1355066617/2500000000 : ℝ)*X 1 1+(157720157/500000000 : ℝ)*X 1 2+(4150866513/10000000000 : ℝ)*X 2 0+(1355066617/2500000000 : ℝ)*X 2 1+(157720157/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4050033359885290767/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (284697/1250000000000 : ℝ)*(base1) + (478608943/50000000000000 : ℝ)*(base19) + (969415329/100000000000000 : ℝ)*(base23) + (104340417/100000000000000 : ℝ)*(upper3) + (146113491/100000000000000 : ℝ)*(upper5) + (686342839885133/100000000000000 : ℝ)*(major0) + (686342839885133/100000000000000 : ℝ)*(major1) + (686342839885133/100000000000000 : ℝ)*(major2) + (477113952594927/50000000000000 : ℝ)*(sp0) + (38169222488977/4000000000000 : ℝ)*(sp1) + (477115275013491/50000000000000 : ℝ)*(sp2) + (418452499026857/100000000000000 : ℝ)*(sp3) + (3637028217/100000000000000 : ℝ)*(sp4) + (1503524223/100000000000000 : ℝ)*(sp7) + (10461350633171/2500000000000 : ℝ)*(f.failure) + (954231519442311/100000000000000 : ℝ)*(f.sum) + (5608114732633/4000000000000000000000000000 : ℝ)*base66 + (17640332983367/8000000000000000000000000000 : ℝ)*base67 + (64520555135367/8000000000000000000000000000 : ℝ)*base69 + (10391305023367/8000000000000000000000000000 : ℝ)*base71 + (8638796528633/4000000000000000000000000000 : ℝ)*base74 + (49628765647367/8000000000000000000000000000 : ℝ)*base75 + (32337537287367/8000000000000000000000000000 : ℝ)*base77 + (11684071703367/8000000000000000000000000000 : ℝ)*base79 + (4659710492633/4000000000000000000000000000 : ℝ)*base82 + (101813/250000000000000000000 : ℝ)*base90 + (101813/250000000000000000000 : ℝ)*base92 + (101813/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6087063564267711435939/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (682947131/50000000000000 : ℝ)*(base19) + (1373928451/100000000000000 : ℝ)*(base23) + (30401343/100000000000000 : ℝ)*(base32) + (204355169/100000000000000 : ℝ)*(upper3) + (84850121/50000000000000 : ℝ)*(upper5) + (361934227114271/50000000000000 : ℝ)*(major0) + (361934227114271/50000000000000 : ℝ)*(major1) + (361934227114271/50000000000000 : ℝ)*(major2) + (1779588931/50000000000000 : ℝ)*(sp1) + (384888651/10000000000000 : ℝ)*(sp2) + (1006403816397487/100000000000000 : ℝ)*(sp4) + (1006398891325363/100000000000000 : ℝ)*(sp5) + (503199296791263/50000000000000 : ℝ)*(sp6) + (44133285875613/10000000000000 : ℝ)*(sp7) + (441332889157473/100000000000000 : ℝ)*(f.failure) + (1006403816397487/100000000000000 : ℝ)*(f.sum) + (3746158417229/2000000000000000000000000000 : ℝ)*base65 + (22298369327229/4000000000000000000000000000 : ℝ)*base67 + (7587999871229/4000000000000000000000000000 : ℝ)*base69 + (12388698719229/4000000000000000000000000000 : ℝ)*base71 + (10150385839229/2000000000000000000000000000 : ℝ)*base73 + (10736316343229/4000000000000000000000000000 : ℝ)*base75 + (13410691271229/4000000000000000000000000000 : ℝ)*base77 + (966372911229/4000000000000000000000000000 : ℝ)*base79 + (5503438231229/2000000000000000000000000000 : ℝ)*base81 + (50727319/10000000000000000000000 : ℝ)*base90 + (50727319/10000000000000000000000 : ℝ)*base92 + (50727319/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1520_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (293/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25381/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1520_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1520_s1_0 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-914478851/5000000000 : ℝ)*x 0 + (278262451/500000000 : ℝ)*x 1 + (5102715031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914478851/5000000000 : ℝ)^4537 ≤ (11146648978373/100000000000000 : ℝ)^3513 := by
    have hnat : (914478851 : ℕ)^4537*100000000000000^3513 ≤ 11146648978373^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914478851 5000000000 11146648978373 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278262451/500000000 : ℝ)^4537 ≤ (46913326102837/100000000000000 : ℝ)^3513 := by
    have hnat : (278262451 : ℕ)^4537*100000000000000^3513 ≤ 46913326102837^3513*500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278262451 500000000 46913326102837 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5102715031/10000000000 : ℝ)^4537 ≤ (41940024902821/100000000000000 : ℝ)^3513 := by
    have hnat : (5102715031 : ℕ)^4537*100000000000000^3513 ≤ 41940024902821^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5102715031 10000000000 41940024902821 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-914478851/5000000000 : ℝ), (278262451/500000000 : ℝ), (5102715031/10000000000 : ℝ)] ![(11146648978373/100000000000000 : ℝ), (46913326102837/100000000000000 : ℝ), (41940024902821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-914478851/5000000000 : ℝ)|^4537 ≤ (11146648978373/100000000000000 : ℝ)^3513
        have hw : |(-914478851/5000000000 : ℝ)|=(914478851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278262451/500000000 : ℝ)|^4537 ≤ (46913326102837/100000000000000 : ℝ)^3513
        have hw : |(278262451/500000000 : ℝ)|=(278262451/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5102715031/10000000000 : ℝ)|^4537 ≤ (41940024902821/100000000000000 : ℝ)^3513
        have hw : |(5102715031/10000000000 : ℝ)|=(5102715031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s1_1 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692585963/5000000000 : ℝ)*x 0 + (-2072270897/10000000000 : ℝ)*x 1 + (5102715373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692585963/5000000000 : ℝ)^4537 ≤ (8992434158481/20000000000000 : ℝ)^3513 := by
    have hnat : (2692585963 : ℕ)^4537*20000000000000^3513 ≤ 8992434158481^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692585963 5000000000 8992434158481 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072270897/10000000000 : ℝ)^4537 ≤ (2619560132207/20000000000000 : ℝ)^3513 := by
    have hnat : (2072270897 : ℕ)^4537*20000000000000^3513 ≤ 2619560132207^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072270897 10000000000 2619560132207 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5102715373/10000000000 : ℝ)^4537 ≤ (20970014266567/50000000000000 : ℝ)^3513 := by
    have hnat : (5102715373 : ℕ)^4537*50000000000000^3513 ≤ 20970014266567^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5102715373 10000000000 20970014266567 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692585963/5000000000 : ℝ), (-2072270897/10000000000 : ℝ), (5102715373/10000000000 : ℝ)] ![(8992434158481/20000000000000 : ℝ), (2619560132207/20000000000000 : ℝ), (20970014266567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692585963/5000000000 : ℝ)|^4537 ≤ (8992434158481/20000000000000 : ℝ)^3513
        have hw : |(2692585963/5000000000 : ℝ)|=(2692585963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2072270897/10000000000 : ℝ)|^4537 ≤ (2619560132207/20000000000000 : ℝ)^3513
        have hw : |(-2072270897/10000000000 : ℝ)|=(2072270897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5102715373/10000000000 : ℝ)|^4537 ≤ (20970014266567/50000000000000 : ℝ)^3513
        have hw : |(5102715373/10000000000 : ℝ)|=(5102715373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s1_2 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336573281/625000000 : ℝ)*x 0 + (5102714883/10000000000 : ℝ)*x 1 + (-2072270781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336573281/625000000 : ℝ)^4537 ≤ (44962176938697/100000000000000 : ℝ)^3513 := by
    have hnat : (336573281 : ℕ)^4537*100000000000000^3513 ≤ 44962176938697^3513*625000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336573281 625000000 44962176938697 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5102714883/10000000000 : ℝ)^4537 ≤ (1310625729119/3125000000000 : ℝ)^3513 := by
    have hnat : (5102714883 : ℕ)^4537*3125000000000^3513 ≤ 1310625729119^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5102714883 10000000000 1310625729119 3125000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072270781/10000000000 : ℝ)^4537 ≤ (13097799714143/100000000000000 : ℝ)^3513 := by
    have hnat : (2072270781 : ℕ)^4537*100000000000000^3513 ≤ 13097799714143^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072270781 10000000000 13097799714143 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336573281/625000000 : ℝ), (5102714883/10000000000 : ℝ), (-2072270781/10000000000 : ℝ)] ![(44962176938697/100000000000000 : ℝ), (1310625729119/3125000000000 : ℝ), (13097799714143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336573281/625000000 : ℝ)|^4537 ≤ (44962176938697/100000000000000 : ℝ)^3513
        have hw : |(336573281/625000000 : ℝ)|=(336573281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5102714883/10000000000 : ℝ)|^4537 ≤ (1310625729119/3125000000000 : ℝ)^3513
        have hw : |(5102714883/10000000000 : ℝ)|=(5102714883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072270781/10000000000 : ℝ)|^4537 ≤ (13097799714143/100000000000000 : ℝ)^3513
        have hw : |(-2072270781/10000000000 : ℝ)|=(2072270781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s1_3 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4246692607/10000000000 : ℝ)*x 0 + (1873394581/5000000000 : ℝ)*x 1 + (600192421/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4246692607/10000000000 : ℝ)^4537 ≤ (33085052193703/100000000000000 : ℝ)^3513 := by
    have hnat : (4246692607 : ℕ)^4537*100000000000000^3513 ≤ 33085052193703^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246692607 10000000000 33085052193703 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1873394581/5000000000 : ℝ)^4537 ≤ (7035998377969/25000000000000 : ℝ)^3513 := by
    have hnat : (1873394581 : ℕ)^4537*25000000000000^3513 ≤ 7035998377969^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873394581 5000000000 7035998377969 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600192421/1250000000 : ℝ)^4537 ≤ (9692738570243/25000000000000 : ℝ)^3513 := by
    have hnat : (600192421 : ℕ)^4537*25000000000000^3513 ≤ 9692738570243^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600192421 1250000000 9692738570243 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4246692607/10000000000 : ℝ), (1873394581/5000000000 : ℝ), (600192421/1250000000 : ℝ)] ![(33085052193703/100000000000000 : ℝ), (7035998377969/25000000000000 : ℝ), (9692738570243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4246692607/10000000000 : ℝ)|^4537 ≤ (33085052193703/100000000000000 : ℝ)^3513
        have hw : |(4246692607/10000000000 : ℝ)|=(4246692607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1873394581/5000000000 : ℝ)|^4537 ≤ (7035998377969/25000000000000 : ℝ)^3513
        have hw : |(1873394581/5000000000 : ℝ)|=(1873394581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600192421/1250000000 : ℝ)|^4537 ≤ (9692738570243/25000000000000 : ℝ)^3513
        have hw : |(600192421/1250000000 : ℝ)|=(600192421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s1_4 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-114327793/625000000 : ℝ)*x 0 + (5107830081/10000000000 : ℝ)*x 1 + (695006599/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114327793/625000000 : ℝ)^4537 ≤ (5574453952007/50000000000000 : ℝ)^3513 := by
    have hnat : (114327793 : ℕ)^4537*50000000000000^3513 ≤ 5574453952007^3513*625000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114327793 625000000 5574453952007 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5107830081/10000000000 : ℝ)^4537 ≤ (20997164419547/50000000000000 : ℝ)^3513 := by
    have hnat : (5107830081 : ℕ)^4537*50000000000000^3513 ≤ 20997164419547^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5107830081 10000000000 20997164419547 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (695006599/1250000000 : ℝ)^4537 ≤ (46856763246121/100000000000000 : ℝ)^3513 := by
    have hnat : (695006599 : ℕ)^4537*100000000000000^3513 ≤ 46856763246121^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695006599 1250000000 46856763246121 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114327793/625000000 : ℝ), (5107830081/10000000000 : ℝ), (695006599/1250000000 : ℝ)] ![(5574453952007/50000000000000 : ℝ), (20997164419547/50000000000000 : ℝ), (46856763246121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114327793/625000000 : ℝ)|^4537 ≤ (5574453952007/50000000000000 : ℝ)^3513
        have hw : |(-114327793/625000000 : ℝ)|=(114327793/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5107830081/10000000000 : ℝ)|^4537 ≤ (20997164419547/50000000000000 : ℝ)^3513
        have hw : |(5107830081/10000000000 : ℝ)|=(5107830081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(695006599/1250000000 : ℝ)|^4537 ≤ (46856763246121/100000000000000 : ℝ)^3513
        have hw : |(695006599/1250000000 : ℝ)|=(695006599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s1_5 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263227743/10000000000 : ℝ)*x 0 + (-1614932903/10000000000 : ℝ)*x 1 + (86875827/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263227743/10000000000 : ℝ)^4537 ≤ (43651613601731/100000000000000 : ℝ)^3513 := by
    have hnat : (5263227743 : ℕ)^4537*100000000000000^3513 ≤ 43651613601731^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263227743 10000000000 43651613601731 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1614932903/10000000000 : ℝ)^4537 ≤ (1898324330181/20000000000000 : ℝ)^3513 := by
    have hnat : (1614932903 : ℕ)^4537*20000000000000^3513 ≤ 1898324330181^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614932903 10000000000 1898324330181 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86875827/156250000 : ℝ)^4537 ≤ (4685676472633/10000000000000 : ℝ)^3513 := by
    have hnat : (86875827 : ℕ)^4537*10000000000000^3513 ≤ 4685676472633^3513*156250000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86875827 156250000 4685676472633 10000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263227743/10000000000 : ℝ), (-1614932903/10000000000 : ℝ), (86875827/156250000 : ℝ)] ![(43651613601731/100000000000000 : ℝ), (1898324330181/20000000000000 : ℝ), (4685676472633/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263227743/10000000000 : ℝ)|^4537 ≤ (43651613601731/100000000000000 : ℝ)^3513
        have hw : |(5263227743/10000000000 : ℝ)|=(5263227743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1614932903/10000000000 : ℝ)|^4537 ≤ (1898324330181/20000000000000 : ℝ)^3513
        have hw : |(-1614932903/10000000000 : ℝ)|=(1614932903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(86875827/156250000 : ℝ)|^4537 ≤ (4685676472633/10000000000000 : ℝ)^3513
        have hw : |(86875827/156250000 : ℝ)|=(86875827/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s1_6 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526322747/1000000000 : ℝ)*x 0 + (5560053077/10000000000 : ℝ)*x 1 + (-64597323/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526322747/1000000000 : ℝ)^4537 ≤ (43651610677569/100000000000000 : ℝ)^3513 := by
    have hnat : (526322747 : ℕ)^4537*100000000000000^3513 ≤ 43651610677569^3513*1000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526322747 1000000000 43651610677569 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5560053077/10000000000 : ℝ)^4537 ≤ (46856766348029/100000000000000 : ℝ)^3513 := by
    have hnat : (5560053077 : ℕ)^4537*100000000000000^3513 ≤ 46856766348029^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5560053077 10000000000 46856766348029 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64597323/400000000 : ℝ)^4537 ≤ (949162295649/10000000000000 : ℝ)^3513 := by
    have hnat : (64597323 : ℕ)^4537*10000000000000^3513 ≤ 949162295649^3513*400000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64597323 400000000 949162295649 10000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526322747/1000000000 : ℝ), (5560053077/10000000000 : ℝ), (-64597323/400000000 : ℝ)] ![(43651610677569/100000000000000 : ℝ), (46856766348029/100000000000000 : ℝ), (949162295649/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526322747/1000000000 : ℝ)|^4537 ≤ (43651610677569/100000000000000 : ℝ)^3513
        have hw : |(526322747/1000000000 : ℝ)|=(526322747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5560053077/10000000000 : ℝ)|^4537 ≤ (46856766348029/100000000000000 : ℝ)^3513
        have hw : |(5560053077/10000000000 : ℝ)|=(5560053077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64597323/400000000 : ℝ)|^4537 ≤ (949162295649/10000000000000 : ℝ)^3513
        have hw : |(-64597323/400000000 : ℝ)|=(64597323/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s1_7 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2123674061/5000000000 : ℝ)*x 0 + (598734447/1250000000 : ℝ)*x 1 + (3758637679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123674061/5000000000 : ℝ)^4537 ≤ (4136455992669/12500000000000 : ℝ)^3513 := by
    have hnat : (2123674061 : ℕ)^4537*12500000000000^3513 ≤ 4136455992669^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123674061 5000000000 4136455992669 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598734447/1250000000 : ℝ)^4537 ≤ (38649362975989/100000000000000 : ℝ)^3513 := by
    have hnat : (598734447 : ℕ)^4537*100000000000000^3513 ≤ 38649362975989^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598734447 1250000000 38649362975989 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3758637679/10000000000 : ℝ)^4537 ≤ (7064747267041/25000000000000 : ℝ)^3513 := by
    have hnat : (3758637679 : ℕ)^4537*25000000000000^3513 ≤ 7064747267041^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3758637679 10000000000 7064747267041 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123674061/5000000000 : ℝ), (598734447/1250000000 : ℝ), (3758637679/10000000000 : ℝ)] ![(4136455992669/12500000000000 : ℝ), (38649362975989/100000000000000 : ℝ), (7064747267041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123674061/5000000000 : ℝ)|^4537 ≤ (4136455992669/12500000000000 : ℝ)^3513
        have hw : |(2123674061/5000000000 : ℝ)|=(2123674061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598734447/1250000000 : ℝ)|^4537 ≤ (38649362975989/100000000000000 : ℝ)^3513
        have hw : |(598734447/1250000000 : ℝ)|=(598734447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3758637679/10000000000 : ℝ)|^4537 ≤ (7064747267041/25000000000000 : ℝ)^3513
        have hw : |(3758637679/10000000000 : ℝ)|=(3758637679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1520_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25381/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (293/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (4231/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18247/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25381/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (293/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25381/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (293/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25381/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (293/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25381/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (293/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25381/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (293/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25381/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (293/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (293/10000 : ℝ) ^ (4535/1024 : ℝ) ≤ (16225566235371/100000000000000000000 : ℝ) := by
    have hpowers : (293/10000 : ℝ)^4535 ≤ (16225566235371/100000000000000000000 : ℝ)^1024 := by
      have hnat : (293 : ℕ)^4535*100000000000000000000^1024 ≤ 16225566235371^1024*10000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        293 10000 16225566235371 100000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (293/10000 : ℝ)) (X := (16225566235371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25381/100000 : ℝ) ^ (4535/1024 : ℝ) ≤ (115268674656537593/50000000000000000000 : ℝ) := by
    have hpowers : (25381/100000 : ℝ)^4535 ≤ (115268674656537593/50000000000000000000 : ℝ)^1024 := by
      have hnat : (25381 : ℕ)^4535*50000000000000000000^1024 ≤ 115268674656537593^1024*100000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25381 100000 115268674656537593 50000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25381/100000 : ℝ)) (X := (115268674656537593/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000016225566235371/50000000000000000000 : ℝ) ≤ (10000000732744333/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (50000016225566235371/50000000000000000000 : ℝ)^1024 ≤ (10000000732744333/10000000000000000 : ℝ)^4535 := by
      have hnat : (50000016225566235371 : ℕ)^1024*10000000000000000^4535 ≤ 10000000732744333^4535*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000016225566235371 50000000000000000000 10000000732744333 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000732744333/10000000000000000 : ℝ)) (X := (50000016225566235371/50000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100230553574879310557/100000000000000000000 : ℝ) ≤ (10005201244679281/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (100230553574879310557/100000000000000000000 : ℝ)^1024 ≤ (10005201244679281/10000000000000000 : ℝ)^4535 := by
      have hnat : (100230553574879310557 : ℕ)^1024*10000000000000000^4535 ≤ 10005201244679281^4535*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100230553574879310557 100000000000000000000 10005201244679281 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005201244679281/10000000000000000 : ℝ)) (X := (100230553574879310557/100000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25115268674656537593/25000000000000000000 : ℝ) ≤ (10010401756614229/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (25115268674656537593/25000000000000000000 : ℝ)^1024 ≤ (10010401756614229/10000000000000000 : ℝ)^4535 := by
      have hnat : (25115268674656537593 : ℕ)^1024*10000000000000000^4535 ≤ 10010401756614229^4535*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25115268674656537593 25000000000000000000 10010401756614229 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010401756614229/10000000000000000 : ℝ)) (X := (25115268674656537593/25000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(16225566235371/100000000000000000000 : ℝ) ≤ ((20407231040991293173/20410000000000000000 : ℝ)+2*(118193453067/51025000000000 : ℝ)*(293/10000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (20407231040991293173/20410000000000000000 : ℝ)+2*(118193453067/51025000000000 : ℝ)*(293/10000 : ℝ)=(10000000732744333/10000000000000000 : ℝ) by norm_num, show 1+2*(16225566235371/100000000000000000000 : ℝ)=(50000016225566235371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(115268674656537593/50000000000000000000 : ℝ)+(16225566235371/100000000000000000000 : ℝ) ≤ ((20407231040991293173/20410000000000000000 : ℝ)+(118193453067/51025000000000 : ℝ)*((25381/100000 : ℝ)+(293/10000 : ℝ)))^(4535/1024 : ℝ) := by
    rw [show (20407231040991293173/20410000000000000000 : ℝ)+(118193453067/51025000000000 : ℝ)*((25381/100000 : ℝ)+(293/10000 : ℝ))=(10005201244679281/10000000000000000 : ℝ) by norm_num, show 1+(115268674656537593/50000000000000000000 : ℝ)+(16225566235371/100000000000000000000 : ℝ)=(100230553574879310557/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(115268674656537593/50000000000000000000 : ℝ) ≤ ((20407231040991293173/20410000000000000000 : ℝ)+2*(118193453067/51025000000000 : ℝ)*(25381/100000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (20407231040991293173/20410000000000000000 : ℝ)+2*(118193453067/51025000000000 : ℝ)*(25381/100000 : ℝ)=(10010401756614229/10000000000000000 : ℝ) by norm_num, show 1+2*(115268674656537593/50000000000000000000 : ℝ)=(25115268674656537593/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20407231040991293173/20410000000000000000 : ℝ)*(X 1 0+X 2 0)+(118193453067/51025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (293/10000 : ℝ)) (hi := (25381/100000 : ℝ)) (c := (20407231040991293173/20410000000000000000 : ℝ)) (alpha := (118193453067/51025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20407231040991293173/20410000000000000000 : ℝ)*(X 0 1+X 2 1)+(118193453067/51025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (293/10000 : ℝ)) (hi := (25381/100000 : ℝ)) (c := (20407231040991293173/20410000000000000000 : ℝ)) (alpha := (118193453067/51025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20407231040991293173/20410000000000000000 : ℝ)*(X 0 2+X 1 2)+(118193453067/51025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (293/10000 : ℝ)) (hi := (25381/100000 : ℝ)) (c := (20407231040991293173/20410000000000000000 : ℝ)) (alpha := (118193453067/51025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-914478851/5000000000 : ℝ)*X 0 0+(278262451/500000000 : ℝ)*X 0 1+(5102715031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2692585963/5000000000 : ℝ)*X 1 0+(-2072270897/10000000000 : ℝ)*X 1 1+(5102715373/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((336573281/625000000 : ℝ)*X 2 0+(5102714883/10000000000 : ℝ)*X 2 1+(-2072270781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4246692607/10000000000 : ℝ)*X 0 0+(1873394581/5000000000 : ℝ)*X 0 1+(600192421/1250000000 : ℝ)*X 0 2+(4246692607/10000000000 : ℝ)*X 1 0+(1873394581/5000000000 : ℝ)*X 1 1+(600192421/1250000000 : ℝ)*X 1 2+(4246692607/10000000000 : ℝ)*X 2 0+(1873394581/5000000000 : ℝ)*X 2 1+(600192421/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-114327793/625000000 : ℝ)*X 0 0+(5107830081/10000000000 : ℝ)*X 0 1+(695006599/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5263227743/10000000000 : ℝ)*X 1 0+(-1614932903/10000000000 : ℝ)*X 1 1+(86875827/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((526322747/1000000000 : ℝ)*X 2 0+(5560053077/10000000000 : ℝ)*X 2 1+(-64597323/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2123674061/5000000000 : ℝ)*X 0 0+(598734447/1250000000 : ℝ)*X 0 1+(3758637679/10000000000 : ℝ)*X 0 2+(2123674061/5000000000 : ℝ)*X 1 0+(598734447/1250000000 : ℝ)*X 1 1+(3758637679/10000000000 : ℝ)*X 1 2+(2123674061/5000000000 : ℝ)*X 2 0+(598734447/1250000000 : ℝ)*X 2 1+(3758637679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37367959115981963162351493/4906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1384866777/100000000000000 : ℝ)*(base19) + (1540547603/100000000000000 : ℝ)*(base23) + (119034399/100000000000000 : ℝ)*(upper3) + (984969/2500000000000 : ℝ)*(upper4) + (169480789/100000000000000 : ℝ)*(upper5) + (194383255643811/12500000000000 : ℝ)*(major0) + (194383255643811/12500000000000 : ℝ)*(major1) + (194383255643811/12500000000000 : ℝ)*(major2) + (540503769822671/25000000000000 : ℝ)*(sp0) + (1081013768963471/50000000000000 : ℝ)*(sp1) + (432405476449223/20000000000000 : ℝ)*(sp2) + (237024312722607/25000000000000 : ℝ)*(sp3) + (2768700607/20000000000000 : ℝ)*(sp4) + (1132547369/20000000000000 : ℝ)*(sp7) + (948102913627273/100000000000000 : ℝ)*(f.failure) + (1081014461396859/50000000000000 : ℝ)*(f.sum) + (2126442363231/392500000000000000000000000 : ℝ)*base66 + (99582606944428669/19625000000000000000000000000000 : ℝ)*base68 + (157723290704928669/19625000000000000000000000000000 : ℝ)*base70 + (246186981606803669/19625000000000000000000000000000 : ℝ)*base72 + (2354322935001/392500000000000000000000000 : ℝ)*base74 + (91331610379178669/19625000000000000000000000000000 : ℝ)*base76 + (28416653036303669/19625000000000000000000000000000 : ℝ)*base78 + (77719376466821331/19625000000000000000000000000000 : ℝ)*base79 + (1308208261043/196250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (61123281/10000000000000000000000 : ℝ)*base89 + (61123281/10000000000000000000000 : ℝ)*base91 + (61123281/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (268463029980589426223467581/39250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (672761807/50000000000000 : ℝ)*(base19) + (42456179/3125000000000 : ℝ)*(base23) + (9243247/5000000000000 : ℝ)*(upper3) + (2863/4882812500 : ℝ)*(lower4) + (49880727/50000000000000 : ℝ)*(upper5) + (795251634721687/50000000000000 : ℝ)*(major0) + (795251634721687/50000000000000 : ℝ)*(major1) + (795251634721687/50000000000000 : ℝ)*(major2) + (2419515239/25000000000000 : ℝ)*(sp1) + (10384489143/100000000000000 : ℝ)*(sp2) + (2211297796842357/100000000000000 : ℝ)*(sp4) + (2211286773257787/100000000000000 : ℝ)*(sp5) + (1105643026877743/50000000000000 : ℝ)*(sp6) + (484854257025153/50000000000000 : ℝ)*(sp7) + (484854257025153/50000000000000 : ℝ)*(f.failure) + (2211297796842357/100000000000000 : ℝ)*(f.sum) + (566687410201/196250000000000000000000000 : ℝ)*base65 + (329891526642827473/78500000000000000000000000000000 : ℝ)*base68 + (19659290774672527/78500000000000000000000000000000 : ℝ)*base69 + (641494462888827473/78500000000000000000000000000000 : ℝ)*base72 + (1309295073409/785000000000000000000000000 : ℝ)*base73 + (341610070644672527/78500000000000000000000000000000 : ℝ)*base75 + (254921632942327473/78500000000000000000000000000000 : ℝ)*base78 + (469496301401827473/78500000000000000000000000000000 : ℝ)*base80 + (3058521109679/785000000000000000000000000 : ℝ)*base81 + (8714359/5000000000000000000000 : ℝ)*base90 + (8714359/5000000000000000000000 : ℝ)*base92 + (8714359/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1520_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25381/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (293/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4231/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18247/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1520_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1520_s2_0 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-370514327/2000000000 : ℝ)*x 0 + (681925467/1250000000 : ℝ)*x 1 + (2598625773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (370514327/2000000000 : ℝ)^4537 ≤ (453314540951/4000000000000 : ℝ)^3513 := by
    have hnat : (370514327 : ℕ)^4537*4000000000000^3513 ≤ 453314540951^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370514327 2000000000 453314540951 4000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681925467/1250000000 : ℝ)^4537 ≤ (45720913217987/100000000000000 : ℝ)^3513 := by
    have hnat : (681925467 : ℕ)^4537*100000000000000^3513 ≤ 45720913217987^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681925467 1250000000 45720913217987 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598625773/5000000000 : ℝ)^4537 ≤ (42946223240397/100000000000000 : ℝ)^3513 := by
    have hnat : (2598625773 : ℕ)^4537*100000000000000^3513 ≤ 42946223240397^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598625773 5000000000 42946223240397 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-370514327/2000000000 : ℝ), (681925467/1250000000 : ℝ), (2598625773/5000000000 : ℝ)] ![(453314540951/4000000000000 : ℝ), (45720913217987/100000000000000 : ℝ), (42946223240397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-370514327/2000000000 : ℝ)|^4537 ≤ (453314540951/4000000000000 : ℝ)^3513
        have hw : |(-370514327/2000000000 : ℝ)|=(370514327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681925467/1250000000 : ℝ)|^4537 ≤ (45720913217987/100000000000000 : ℝ)^3513
        have hw : |(681925467/1250000000 : ℝ)|=(681925467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598625773/5000000000 : ℝ)|^4537 ≤ (42946223240397/100000000000000 : ℝ)^3513
        have hw : |(2598625773/5000000000 : ℝ)|=(2598625773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s2_1 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13392981/25000000 : ℝ)*x 0 + (-79416059/400000000 : ℝ)*x 1 + (5197252111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13392981/25000000 : ℝ)^4537 ≤ (44660697192773/100000000000000 : ℝ)^3513 := by
    have hnat : (13392981 : ℕ)^4537*100000000000000^3513 ≤ 44660697192773^3513*25000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13392981 25000000 44660697192773 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79416059/400000000 : ℝ)^4537 ≤ (12393073526461/100000000000000 : ℝ)^3513 := by
    have hnat : (79416059 : ℕ)^4537*100000000000000^3513 ≤ 12393073526461^3513*400000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79416059 400000000 12393073526461 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5197252111/10000000000 : ℝ)^4537 ≤ (21473114635011/50000000000000 : ℝ)^3513 := by
    have hnat : (5197252111 : ℕ)^4537*50000000000000^3513 ≤ 21473114635011^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197252111 10000000000 21473114635011 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13392981/25000000 : ℝ), (-79416059/400000000 : ℝ), (5197252111/10000000000 : ℝ)] ![(44660697192773/100000000000000 : ℝ), (12393073526461/100000000000000 : ℝ), (21473114635011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13392981/25000000 : ℝ)|^4537 ≤ (44660697192773/100000000000000 : ℝ)^3513
        have hw : |(13392981/25000000 : ℝ)|=(13392981/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79416059/400000000 : ℝ)|^4537 ≤ (12393073526461/100000000000000 : ℝ)^3513
        have hw : |(-79416059/400000000 : ℝ)|=(79416059/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5197252111/10000000000 : ℝ)|^4537 ≤ (21473114635011/50000000000000 : ℝ)^3513
        have hw : |(5197252111/10000000000 : ℝ)|=(5197252111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s2_2 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5357193201/10000000000 : ℝ)*x 0 + (5197251613/10000000000 : ℝ)*x 1 + (-248175133/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357193201/10000000000 : ℝ)^4537 ≤ (22330352908413/50000000000000 : ℝ)^3513 := by
    have hnat : (5357193201 : ℕ)^4537*50000000000000^3513 ≤ 22330352908413^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357193201 10000000000 22330352908413 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5197251613/10000000000 : ℝ)^4537 ≤ (8589244791083/20000000000000 : ℝ)^3513 := by
    have hnat : (5197251613 : ℕ)^4537*20000000000000^3513 ≤ 8589244791083^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197251613 10000000000 8589244791083 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248175133/1250000000 : ℝ)^4537 ≤ (12393070213143/100000000000000 : ℝ)^3513 := by
    have hnat : (248175133 : ℕ)^4537*100000000000000^3513 ≤ 12393070213143^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248175133 1250000000 12393070213143 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357193201/10000000000 : ℝ), (5197251613/10000000000 : ℝ), (-248175133/1250000000 : ℝ)] ![(22330352908413/50000000000000 : ℝ), (8589244791083/20000000000000 : ℝ), (12393070213143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357193201/10000000000 : ℝ)|^4537 ≤ (22330352908413/50000000000000 : ℝ)^3513
        have hw : |(5357193201/10000000000 : ℝ)|=(5357193201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5197251613/10000000000 : ℝ)|^4537 ≤ (8589244791083/20000000000000 : ℝ)^3513
        have hw : |(5197251613/10000000000 : ℝ)|=(5197251613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-248175133/1250000000 : ℝ)|^4537 ≤ (12393070213143/100000000000000 : ℝ)^3513
        have hw : |(-248175133/1250000000 : ℝ)|=(248175133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s2_3 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42636679/100000000 : ℝ)*x 0 + (994471729/2500000000 : ℝ)*x 1 + (285410727/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42636679/100000000 : ℝ)^4537 ≤ (2078497000909/6250000000000 : ℝ)^3513 := by
    have hnat : (42636679 : ℕ)^4537*6250000000000^3513 ≤ 2078497000909^3513*100000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42636679 100000000 2078497000909 6250000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994471729/2500000000 : ℝ)^4537 ≤ (30405742862731/100000000000000 : ℝ)^3513 := by
    have hnat : (994471729 : ℕ)^4537*100000000000000^3513 ≤ 30405742862731^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994471729 2500000000 30405742862731 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285410727/625000000 : ℝ)^4537 ≤ (4542288137809/12500000000000 : ℝ)^3513 := by
    have hnat : (285410727 : ℕ)^4537*12500000000000^3513 ≤ 4542288137809^3513*625000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285410727 625000000 4542288137809 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42636679/100000000 : ℝ), (994471729/2500000000 : ℝ), (285410727/625000000 : ℝ)] ![(2078497000909/6250000000000 : ℝ), (30405742862731/100000000000000 : ℝ), (4542288137809/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42636679/100000000 : ℝ)|^4537 ≤ (2078497000909/6250000000000 : ℝ)^3513
        have hw : |(42636679/100000000 : ℝ)|=(42636679/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994471729/2500000000 : ℝ)|^4537 ≤ (30405742862731/100000000000000 : ℝ)^3513
        have hw : |(994471729/2500000000 : ℝ)|=(994471729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(285410727/625000000 : ℝ)|^4537 ≤ (4542288137809/12500000000000 : ℝ)^3513
        have hw : |(285410727/625000000 : ℝ)|=(285410727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s2_4 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-92631027/500000000 : ℝ)*x 0 + (5198854197/10000000000 : ℝ)*x 1 + (2726893867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92631027/500000000 : ℝ)^4537 ≤ (5666624949919/50000000000000 : ℝ)^3513 := by
    have hnat : (92631027 : ℕ)^4537*50000000000000^3513 ≤ 5666624949919^3513*500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92631027 500000000 5666624949919 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5198854197/10000000000 : ℝ)^4537 ≤ (21481663672521/50000000000000 : ℝ)^3513 := by
    have hnat : (5198854197 : ℕ)^4537*50000000000000^3513 ≤ 21481663672521^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198854197 10000000000 21481663672521 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726893867/5000000000 : ℝ)^4537 ≤ (22851711368119/50000000000000 : ℝ)^3513 := by
    have hnat : (2726893867 : ℕ)^4537*50000000000000^3513 ≤ 22851711368119^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726893867 5000000000 22851711368119 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92631027/500000000 : ℝ), (5198854197/10000000000 : ℝ), (2726893867/5000000000 : ℝ)] ![(5666624949919/50000000000000 : ℝ), (21481663672521/50000000000000 : ℝ), (22851711368119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92631027/500000000 : ℝ)|^4537 ≤ (5666624949919/50000000000000 : ℝ)^3513
        have hw : |(-92631027/500000000 : ℝ)|=(92631027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5198854197/10000000000 : ℝ)|^4537 ≤ (21481663672521/50000000000000 : ℝ)^3513
        have hw : |(5198854197/10000000000 : ℝ)|=(5198854197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726893867/5000000000 : ℝ)|^4537 ≤ (22851711368119/50000000000000 : ℝ)^3513
        have hw : |(2726893867/5000000000 : ℝ)|=(2726893867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s2_5 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289327779/10000000000 : ℝ)*x 0 + (-27013531/156250000 : ℝ)*x 1 + (5453788407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289327779/10000000000 : ℝ)^4537 ≤ (43931378534359/100000000000000 : ℝ)^3513 := by
    have hnat : (5289327779 : ℕ)^4537*100000000000000^3513 ≤ 43931378534359^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289327779 10000000000 43931378534359 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27013531/156250000 : ℝ)^4537 ≤ (10365191437939/100000000000000 : ℝ)^3513 := by
    have hnat : (27013531 : ℕ)^4537*100000000000000^3513 ≤ 10365191437939^3513*156250000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27013531 156250000 10365191437939 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453788407/10000000000 : ℝ)^4537 ≤ (45703430020007/100000000000000 : ℝ)^3513 := by
    have hnat : (5453788407 : ℕ)^4537*100000000000000^3513 ≤ 45703430020007^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453788407 10000000000 45703430020007 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289327779/10000000000 : ℝ), (-27013531/156250000 : ℝ), (5453788407/10000000000 : ℝ)] ![(43931378534359/100000000000000 : ℝ), (10365191437939/100000000000000 : ℝ), (45703430020007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289327779/10000000000 : ℝ)|^4537 ≤ (43931378534359/100000000000000 : ℝ)^3513
        have hw : |(5289327779/10000000000 : ℝ)|=(5289327779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27013531/156250000 : ℝ)|^4537 ≤ (10365191437939/100000000000000 : ℝ)^3513
        have hw : |(-27013531/156250000 : ℝ)|=(27013531/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453788407/10000000000 : ℝ)|^4537 ≤ (45703430020007/100000000000000 : ℝ)^3513
        have hw : |(5453788407/10000000000 : ℝ)|=(5453788407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s2_6 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644664233/5000000000 : ℝ)*x 0 + (2726894027/5000000000 : ℝ)*x 1 + (-432216381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644664233/5000000000 : ℝ)^4537 ≤ (43931385903583/100000000000000 : ℝ)^3513 := by
    have hnat : (2644664233 : ℕ)^4537*100000000000000^3513 ≤ 43931385903583^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644664233 5000000000 43931385903583 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726894027/5000000000 : ℝ)^4537 ≤ (22851713099773/50000000000000 : ℝ)^3513 := by
    have hnat : (2726894027 : ℕ)^4537*50000000000000^3513 ≤ 22851713099773^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726894027 5000000000 22851713099773 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432216381/2500000000 : ℝ)^4537 ≤ (10365187876181/100000000000000 : ℝ)^3513 := by
    have hnat : (432216381 : ℕ)^4537*100000000000000^3513 ≤ 10365187876181^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432216381 2500000000 10365187876181 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644664233/5000000000 : ℝ), (2726894027/5000000000 : ℝ), (-432216381/2500000000 : ℝ)] ![(43931385903583/100000000000000 : ℝ), (22851713099773/50000000000000 : ℝ), (10365187876181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644664233/5000000000 : ℝ)|^4537 ≤ (43931385903583/100000000000000 : ℝ)^3513
        have hw : |(2644664233/5000000000 : ℝ)|=(2644664233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726894027/5000000000 : ℝ)|^4537 ≤ (22851713099773/50000000000000 : ℝ)^3513
        have hw : |(2726894027/5000000000 : ℝ)|=(2726894027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-432216381/2500000000 : ℝ)|^4537 ≤ (10365187876181/100000000000000 : ℝ)^3513
        have hw : |(-432216381/2500000000 : ℝ)|=(432216381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s2_7 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1065945709/2500000000 : ℝ)*x 0 + (4562918503/10000000000 : ℝ)*x 1 + (3981571779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065945709/2500000000 : ℝ)^4537 ≤ (33257109816901/100000000000000 : ℝ)^3513 := by
    have hnat : (1065945709 : ℕ)^4537*100000000000000^3513 ≤ 33257109816901^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065945709 2500000000 33257109816901 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4562918503/10000000000 : ℝ)^4537 ≤ (36300766389131/100000000000000 : ℝ)^3513 := by
    have hnat : (4562918503 : ℕ)^4537*100000000000000^3513 ≤ 36300766389131^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4562918503 10000000000 36300766389131 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3981571779/10000000000 : ℝ)^4537 ≤ (3805265473891/12500000000000 : ℝ)^3513 := by
    have hnat : (3981571779 : ℕ)^4537*12500000000000^3513 ≤ 3805265473891^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3981571779 10000000000 3805265473891 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065945709/2500000000 : ℝ), (4562918503/10000000000 : ℝ), (3981571779/10000000000 : ℝ)] ![(33257109816901/100000000000000 : ℝ), (36300766389131/100000000000000 : ℝ), (3805265473891/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065945709/2500000000 : ℝ)|^4537 ≤ (33257109816901/100000000000000 : ℝ)^3513
        have hw : |(1065945709/2500000000 : ℝ)|=(1065945709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4562918503/10000000000 : ℝ)|^4537 ≤ (36300766389131/100000000000000 : ℝ)^3513
        have hw : |(4562918503/10000000000 : ℝ)|=(4562918503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3981571779/10000000000 : ℝ)|^4537 ≤ (3805265473891/12500000000000 : ℝ)^3513
        have hw : |(3981571779/10000000000 : ℝ)|=(3981571779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1520_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4231/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10501/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15967/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4231/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4231/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4231/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4231/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4231/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4231/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4231/50000 : ℝ) ^ (4535/1024 : ℝ) ≤ (1778639927672253/100000000000000000000 : ℝ) := by
    have hpowers : (4231/50000 : ℝ)^4535 ≤ (1778639927672253/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4231 : ℕ)^4535*100000000000000000000^1024 ≤ 1778639927672253^1024*50000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4231 50000 1778639927672253 100000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4231/50000 : ℝ)) (X := (1778639927672253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18247/100000 : ℝ) ^ (4535/1024 : ℝ) ≤ (2138408060997757/4000000000000000000 : ℝ) := by
    have hpowers : (18247/100000 : ℝ)^4535 ≤ (2138408060997757/4000000000000000000 : ℝ)^1024 := by
      have hnat : (18247 : ℕ)^4535*4000000000000000000^1024 ≤ 2138408060997757^1024*100000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18247 100000 2138408060997757 4000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18247/100000 : ℝ)) (X := (2138408060997757/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001778639927672253/50000000000000000000 : ℝ) ≤ (10000080322037767/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (50001778639927672253/50000000000000000000 : ℝ)^1024 ≤ (10000080322037767/10000000000000000 : ℝ)^4535 := by
      have hnat : (50001778639927672253 : ℕ)^1024*10000000000000000^4535 ≤ 10000080322037767^4535*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001778639927672253 50000000000000000000 10000080322037767 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000080322037767/10000000000000000 : ℝ)) (X := (50001778639927672253/50000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027619420726308089/50000000000000000000 : ℝ) ≤ (2000249404553073/2000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (50027619420726308089/50000000000000000000 : ℝ)^1024 ≤ (2000249404553073/2000000000000000 : ℝ)^4535 := by
      have hnat : (50027619420726308089 : ℕ)^1024*2000000000000000^4535 ≤ 2000249404553073^4535*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027619420726308089 50000000000000000000 2000249404553073 2000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000249404553073/2000000000000000 : ℝ)) (X := (50027619420726308089/50000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2002138408060997757/2000000000000000000 : ℝ) ≤ (10002413723492963/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (2002138408060997757/2000000000000000000 : ℝ)^1024 ≤ (10002413723492963/10000000000000000 : ℝ)^4535 := by
      have hnat : (2002138408060997757 : ℕ)^1024*10000000000000000^4535 ≤ 10002413723492963^4535*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2002138408060997757 2000000000000000000 10002413723492963 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002413723492963/10000000000000000 : ℝ)) (X := (2002138408060997757/2000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1778639927672253/100000000000000000000 : ℝ) ≤ ((97831040708025681543/97850000000000000000 : ℝ)+2*(583350363799/489250000000000 : ℝ)*(4231/50000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (97831040708025681543/97850000000000000000 : ℝ)+2*(583350363799/489250000000000 : ℝ)*(4231/50000 : ℝ)=(10000080322037767/10000000000000000 : ℝ) by norm_num, show 1+2*(1778639927672253/100000000000000000000 : ℝ)=(50001778639927672253/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2138408060997757/4000000000000000000 : ℝ)+(1778639927672253/100000000000000000000 : ℝ) ≤ ((97831040708025681543/97850000000000000000 : ℝ)+(583350363799/489250000000000 : ℝ)*((18247/100000 : ℝ)+(4231/50000 : ℝ)))^(4535/1024 : ℝ) := by
    rw [show (97831040708025681543/97850000000000000000 : ℝ)+(583350363799/489250000000000 : ℝ)*((18247/100000 : ℝ)+(4231/50000 : ℝ))=(2000249404553073/2000000000000000 : ℝ) by norm_num, show 1+(2138408060997757/4000000000000000000 : ℝ)+(1778639927672253/100000000000000000000 : ℝ)=(50027619420726308089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2138408060997757/4000000000000000000 : ℝ) ≤ ((97831040708025681543/97850000000000000000 : ℝ)+2*(583350363799/489250000000000 : ℝ)*(18247/100000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (97831040708025681543/97850000000000000000 : ℝ)+2*(583350363799/489250000000000 : ℝ)*(18247/100000 : ℝ)=(10002413723492963/10000000000000000 : ℝ) by norm_num, show 1+2*(2138408060997757/4000000000000000000 : ℝ)=(2002138408060997757/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (97831040708025681543/97850000000000000000 : ℝ)*(X 1 0+X 2 0)+(583350363799/489250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (4231/50000 : ℝ)) (hi := (18247/100000 : ℝ)) (c := (97831040708025681543/97850000000000000000 : ℝ)) (alpha := (583350363799/489250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (97831040708025681543/97850000000000000000 : ℝ)*(X 0 1+X 2 1)+(583350363799/489250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (4231/50000 : ℝ)) (hi := (18247/100000 : ℝ)) (c := (97831040708025681543/97850000000000000000 : ℝ)) (alpha := (583350363799/489250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (97831040708025681543/97850000000000000000 : ℝ)*(X 0 2+X 1 2)+(583350363799/489250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (4231/50000 : ℝ)) (hi := (18247/100000 : ℝ)) (c := (97831040708025681543/97850000000000000000 : ℝ)) (alpha := (583350363799/489250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-370514327/2000000000 : ℝ)*X 0 0+(681925467/1250000000 : ℝ)*X 0 1+(2598625773/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((13392981/25000000 : ℝ)*X 1 0+(-79416059/400000000 : ℝ)*X 1 1+(5197252111/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5357193201/10000000000 : ℝ)*X 2 0+(5197251613/10000000000 : ℝ)*X 2 1+(-248175133/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((42636679/100000000 : ℝ)*X 0 0+(994471729/2500000000 : ℝ)*X 0 1+(285410727/625000000 : ℝ)*X 0 2+(42636679/100000000 : ℝ)*X 1 0+(994471729/2500000000 : ℝ)*X 1 1+(285410727/625000000 : ℝ)*X 1 2+(42636679/100000000 : ℝ)*X 2 0+(994471729/2500000000 : ℝ)*X 2 1+(285410727/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-92631027/500000000 : ℝ)*X 0 0+(5198854197/10000000000 : ℝ)*X 0 1+(2726893867/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289327779/10000000000 : ℝ)*X 1 0+(-27013531/156250000 : ℝ)*X 1 1+(5453788407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644664233/5000000000 : ℝ)*X 2 0+(2726894027/5000000000 : ℝ)*X 2 1+(-432216381/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1065945709/2500000000 : ℝ)*X 0 0+(4562918503/10000000000 : ℝ)*X 0 1+(3981571779/10000000000 : ℝ)*X 0 2+(1065945709/2500000000 : ℝ)*X 1 0+(4562918503/10000000000 : ℝ)*X 1 1+(3981571779/10000000000 : ℝ)*X 1 2+(1065945709/2500000000 : ℝ)*X 2 0+(4562918503/10000000000 : ℝ)*X 2 1+(3981571779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18536007817736858917837943853/2446250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1597578957/100000000000000 : ℝ)*(base19) + (233221171/12500000000000 : ℝ)*(base23) + (117665857/100000000000000 : ℝ)*(upper3) + (83305843/50000000000000 : ℝ)*(upper4) + (84078607/25000000000000 : ℝ)*(upper5) + (2786235481500057/100000000000000 : ℝ)*(major0) + (2786235481500057/100000000000000 : ℝ)*(major1) + (2786235481500057/100000000000000 : ℝ)*(major2) + (968426611992931/25000000000000 : ℝ)*(sp0) + (1936869352191623/50000000000000 : ℝ)*(sp1) + (968434609048209/25000000000000 : ℝ)*(sp2) + (53084882804287/3125000000000 : ℝ)*(sp3) + (423174881/1250000000000 : ℝ)*(sp4) + (707936177/5000000000000 : ℝ)*(sp7) + (424682602115181/25000000000000 : ℝ)*(f.failure) + (968435075490551/25000000000000 : ℝ)*(f.sum) + (120937338477793/24462500000000000000000000000 : ℝ)*base65 + (146386660530853052049/9785000000000000000000000000000000 : ℝ)*base68 + (2656253339293052049/9785000000000000000000000000000000 : ℝ)*base70 + (36078719987673052049/9785000000000000000000000000000000 : ℝ)*base72 + (8329815153591/12231250000000000000000000000 : ℝ)*base74 + (72429191897336947951/9785000000000000000000000000000000 : ℝ)*base75 + (47679597155933052049/9785000000000000000000000000000000 : ℝ)*base78 + (44642612576393052049/9785000000000000000000000000000000 : ℝ)*base80 + (78570261525193/24462500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6539157/2500000000000000000000 : ℝ)*base89 + (6539157/2500000000000000000000 : ℝ)*base91 + (6539157/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1900528235228204747132503167/152890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51896019/50000000000000 : ℝ)*(base19) + (121175927/12500000000000 : ℝ)*(base23) + (184887051/100000000000000 : ℝ)*(lower2) + (77794009/25000000000000 : ℝ)*(upper3) + (131542493/50000000000000 : ℝ)*(lower4) + (88167745096427/3125000000000 : ℝ)*(major0) + (88167745096427/3125000000000 : ℝ)*(major1) + (88167745096427/3125000000000 : ℝ)*(major2) + (16234187061/100000000000000 : ℝ)*(sp2) + (1196192359/100000000000000 : ℝ)*(sp3) + (1961292566818601/50000000000000 : ℝ)*(sp4) + (980646257461291/25000000000000 : ℝ)*(sp5) + (156902717201709/4000000000000 : ℝ)*(sp6) + (172014894198711/10000000000000 : ℝ)*(sp7) + (430037534544867/25000000000000 : ℝ)*(f.failure) + (1961292566818601/50000000000000 : ℝ)*(f.sum) + (91033113310357/12231250000000000000000000000 : ℝ)*base66 + (693064826948746861/305781250000000000000000000000000 : ℝ)*base67 + (155684589722809361/305781250000000000000000000000000 : ℝ)*base69 + (1363636121708746861/305781250000000000000000000000000 : ℝ)*base71 + (73300540956039/24462500000000000000000000000 : ℝ)*base74 + (258506350958440639/305781250000000000000000000000000 : ℝ)*base76 + (1350500072312346889/305781250000000000000000000000000 : ℝ)*base78 + (1809915630262340611/305781250000000000000000000000000 : ℝ)*base79 + (81449317131439/24462500000000000000000000000 : ℝ)*base82 + (26621701/2500000000000000000000 : ℝ)*base90 + (26621701/2500000000000000000000 : ℝ)*base92 + (26621701/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1520_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4231/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10501/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15967/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1520_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1520_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10501/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15967/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1520_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1520_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1520_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10501/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15967/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1520_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
